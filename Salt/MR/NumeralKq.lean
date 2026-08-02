/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S12FuseCompose
import Salt.MR.M4CapWire
import Salt.MR.M4RowsChi
import Salt.MR.USetGChiTS
import Salt.MR.PortClose
import Salt.MR.PortAssembly
import Salt.SW.ZeroFreeReal

/-!
# ⟦ROUTE 3 — THE `Kq` CEILING, LEAF TO THE FENCE⟧ (NUMERAL wave)

`logChowla2_ineffective`'s fifth inner rider is `Kq ≤ e^100`.  `Kq` is
`S12FuseCompose.m4_fuse_hcap_of_capWS_gk`'s opaque `∃ … Kq …, 0 < Kq` —
POSITIVITY ONLY — but the constant is a CLOSED FORM at the bottom of the port:
`PortAssembly.twisted_rect_zero_free_siegel` sets `Kq := 1/(10^8·c₀)` with `c₀`
the zero-free-region width of `Salt.SW.zero_free_region_all'`, and THAT is
`min (1/50456) (1/126848) = 1/126848` at literal `refine` witnesses in
`ZeroFree.lean` :262 and `ZeroFreeReal.lean` :392.

So `Kq = 126848/10^8 = 1.26848·10^{-3}` — against the asked `e^100 ≈ 2.7·10^43`
that is FORTY-SIX ORDERS of room, and the rider is TRUE by a mile.

⟦THE POLARITY, NOTED⟧ the leaf ceiling on `Kq` is a leaf FLOOR on `c₀`
(`1/126848 ≤ c₀`), and a floor is exactly what the `∃` of a zero-free region
does not export (shrinking `c₀` only weakens the region).  That is why the
thirteen twins are needed and why no `min`/`max` trick shortcuts them.

THE CHAIN (bottom to top): `zero_free_region_primitive` /
`zero_free_region_real` → `zero_free_region_all` → `zero_free_region_all'` →
`twisted_rect_zero_free_siegel` (the reciprocal rescale) →
`halasz_primes_chi_pair_of_gates` → `halaszPrimesChi_holds_gated` →
`halaszPrimesChi_pointwise_of_gates` →
`usetGChi_window_meansq_gated_family_perBlock` →
`usetGChi_row_exit_perChi_perBlock` → `m4_rowChi_capstone_perBlock` →
`m4_hcap_at_door_perBlock_gk` → `m4_fuse_hcap_of_capWS_gk`.

Each twin is the landed statement with ONE conjunct added and the landed proof
replayed verbatim against the twin below it.  ⟦IRON RULE 1⟧ every landed
declaration is untouched.

No `sorry`, no `native_decide`, no new axioms.
-/

open scoped BigOperators

-- ⟦BYTE-FAITHFUL REPLAY⟧ every proof body below is the landed proof, copied verbatim so
-- that the twin is auditable against its original line for line; the long lines are the
-- originals' own, and reflowing them would destroy exactly the property that makes the
-- replay checkable.  (Same device as `Salt/Chen/SuperPanelsO.lean`.)
set_option linter.style.longLine false

namespace Salt.SW

set_option maxHeartbeats 800000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open Complex DirichletCharacter Filter Metric in
open scoped LSeries.notation Topology in
/-- **⟦Kq BOUNDED TWIN⟧** `zero_free_region_primitive` + the conjunct `1 / 126848 ≤ c₀`.
the primitive arm, witness `1/50456` (weakened to the chain-common `1/126848`). -/
theorem zero_free_region_primitive_bounded :
    ∃ c₀ : ℝ, 0 < c₀ ∧ 1 / 126848 ≤ c₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ^ 2 ≠ 1 → ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
  refine ⟨1 / 50456, by norm_num, by norm_num, ?_⟩
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

set_option maxHeartbeats 1200000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open Complex DirichletCharacter Filter Metric in
open scoped LSeries.notation Topology in
/-- **⟦Kq BOUNDED TWIN⟧** `zero_free_region_real` + the conjunct `1 / 126848 ≤ c₀`.
the real arm — THE BINDING LEAF, witness `1/126848` exactly. -/
theorem zero_free_region_real_bounded :
    ∃ c₀ : ℝ, 0 < c₀ ∧ 1 / 126848 ≤ c₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ^ 2 = 1 → χ ≠ 1 → ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re → ρ.im ≠ 0 →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
  refine ⟨1 / 126848, by norm_num, by norm_num, ?_⟩
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

set_option maxHeartbeats 800000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open Complex DirichletCharacter Filter Metric in
open scoped LSeries.notation Topology in
/-- **⟦Kq BOUNDED TWIN⟧** `zero_free_region_all` + the conjunct `1 / 126848 ≤ c₀`.
the two arms joined at `min`; the bound survives `le_min`. -/
theorem zero_free_region_all_bounded :
    ∃ c₀ : ℝ, 0 < c₀ ∧ 1 / 126848 ≤ c₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ≠ 1 → ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re → (χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
  obtain ⟨c₁, hc₁, hc₁b, h₁⟩ := zero_free_region_primitive_bounded
  obtain ⟨c₂, hc₂, hc₂b, h₂⟩ := zero_free_region_real_bounded
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, le_min hc₁b hc₂b, ?_⟩
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
    have hb := h₂ q χ hχ hsq hχ1 hzero hre hγ
    have hmin : min c₁ c₂ / Real.log ((q : ℝ) * (|ρ.im| + 2))
        ≤ c₂ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
      rw [div_le_div_iff_of_pos_right hLpos]
      exact min_le_right c₁ c₂
    linarith [hb, hmin]
  · have hb := h₁ q χ hχ hsq hzero hre
    have hmin : min c₁ c₂ / Real.log ((q : ℝ) * (|ρ.im| + 2))
        ≤ c₁ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
      rw [div_le_div_iff_of_pos_right hLpos]
      exact min_le_left c₁ c₂
    linarith [hb, hmin]

set_option maxHeartbeats 800000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open Complex DirichletCharacter Filter Metric in
open scoped LSeries.notation Topology in
/-- **⟦Kq BOUNDED TWIN⟧** `zero_free_region_all'` + the conjunct `1 / 126848 ≤ c₀`.
the imprimitive extension; pass-through. -/
theorem zero_free_region_all'_bounded :
    ∃ c₀ : ℝ, 0 < c₀ ∧ 1 / 126848 ≤ c₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re →
        (χ.primitiveCharacter ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
  obtain ⟨c₀, hc₀pos, hc₀b, hc₀⟩ := zero_free_region_all_bounded
  refine ⟨c₀, hc₀pos, hc₀b, ?_⟩
  intro q hNe χ hχ1 ρ hzero hre hor
  have hρre_pos : 0 < ρ.re := by linarith
  have hzero1 : LFunction χ.primitiveCharacter ρ = 0 :=
    (LFunction_eq_zero_iff_primitive χ hρre_pos (Or.inl hχ1)).mp hzero
  have hf1 : χ.primitiveCharacter.IsPrimitive := primitiveCharacter_isPrimitive χ
  have hχ1' : χ.primitiveCharacter ≠ 1 := fun h =>
    hχ1 (by rw [← changeLevel_primitiveCharacter χ, h, changeLevel_one])
  have hbound := hc₀ χ.conductor χ.primitiveCharacter hf1 hχ1' hzero1 hre hor
  -- modulus monotonicity of the log denominator
  have hf1q : χ.conductor ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (conductor_dvd_level χ)
  have hf1_1 : 1 ≤ χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  set Lf : ℝ := Real.log ((χ.conductor : ℝ) * (|ρ.im| + 2)) with hLfdef
  set Lq : ℝ := Real.log ((q : ℝ) * (|ρ.im| + 2)) with hLqdef
  have hf1R : (1 : ℝ) ≤ (χ.conductor : ℝ) := by exact_mod_cast hf1_1
  have hcondR : (χ.conductor : ℝ) ≤ (q : ℝ) := by exact_mod_cast hf1q
  have hLf_pos : 0 < Lf := by
    rw [hLfdef]; apply Real.log_pos; nlinarith [abs_nonneg ρ.im, hf1R]
  have hLq_pos : 0 < Lq := by
    rw [hLqdef]; apply Real.log_pos; nlinarith [abs_nonneg ρ.im, hf1R, hcondR]
  have hLfq : Lf ≤ Lq := by
    rw [hLfdef, hLqdef]
    apply Real.log_le_log (by nlinarith [abs_nonneg ρ.im, hf1R])
    exact mul_le_mul_of_nonneg_right hcondR (by positivity)
  have hmono : c₀ / Lq ≤ c₀ / Lf := by
    rw [div_le_div_iff₀ hLq_pos hLf_pos]
    exact mul_le_mul_of_nonneg_left hLfq hc₀pos.le
  linarith [hbound, hmono]

end Salt.SW

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

set_option maxHeartbeats 1200000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open Complex MeasureTheory Set ArithmeticFunction DirichletCharacter in
open scoped LSeries.notation in
/-- **⟦Kq BOUNDED TWIN⟧** `twisted_rect_zero_free_siegel` + the conjunct `Kq ≤ 126848 / 10 ^ 8`.
⟦THE RESCALE⟧ `Kq := 1/(10^8·c₀)`, so the leaf LOWER bound becomes the `Kq` CEILING `126848/10^8 = 0.00126848`. -/
theorem twisted_rect_zero_free_siegel_bounded :
    ∃ Kq Ks : ℝ, 0 < Kq ∧ Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q), ψ ≠ 1 → ∀ (A T : ℝ), 1 ≤ A →
      Real.exp (Real.exp 100) ≤ T →
      Real.log (20000 * (vkStripConst q + 8104)) ≤ A * 100 →
      A + 7 ≤ Real.log (Real.log (5 * T + 1)) →
      Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
          ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
      (q : ℝ) ^ ((1 : ℝ) / 16)
          ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      ∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - (1 / 10 ^ 8)
          / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) := by
  obtain ⟨c₀, hc₀0, hc₀b, hc₀⟩ := Salt.SW.zero_free_region_all'_bounded
  obtain ⟨Ks, hKs0, hsg⟩ := siegel_real_carve
  refine ⟨1 / (10 ^ 8 * c₀), 10 ^ 8 * Ks, by positivity, ?_, by positivity, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 10 ^ 8)]
    nlinarith [hc₀b, hc₀0]
  intro q hNe ψ hψ1 A T hA1 hTfloor hAq hAabs hKq hSg ρ hρ0 hρim
  -- the `T`-scale quantities
  have hE0 : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le hE0 hTfloor
  have h5T : Real.exp (Real.exp 100) ≤ 5 * T + 1 := by linarith
  have h5T0 : (0 : ℝ) < 5 * T + 1 := by linarith
  have hLg100 : Real.exp 100 ≤ Real.log (5 * T + 1) := by
    have h := Real.log_le_log hE0 h5T; rwa [Real.log_exp] at h
  have hexp100 : (1 : ℝ) ≤ Real.exp 100 := by
    have := Real.add_one_le_exp (100 : ℝ); linarith
  have hLg1 : (1 : ℝ) ≤ Real.log (5 * T + 1) := by linarith
  have hLg0 : 0 < Real.log (5 * T + 1) := by linarith
  have hℓ100 : (100 : ℝ) ≤ Real.log (Real.log (5 * T + 1)) := by
    have h := Real.log_le_log (Real.exp_pos 100) hLg100; rwa [Real.log_exp] at h
  have hℓ1 : (1 : ℝ) ≤ Real.log (Real.log (5 * T + 1)) := by linarith
  set Lg : ℝ := Real.log (5 * T + 1) with hLgdef
  set ℓ : ℝ := Real.log (Real.log (5 * T + 1)) with hℓdef
  have hLg34 : (1 : ℝ) ≤ Lg ^ ((3 : ℝ) / 4) := Real.one_le_rpow hLg1 (by norm_num)
  have hLg34pos : 0 < Lg ^ ((3 : ℝ) / 4) := by linarith
  have hD3pos : 0 < Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ) := by positivity
  have hD4pos : 0 < Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) := by positivity
  have hD4ge1 : (1 : ℝ) ≤ Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) := by
    have h1 : (1 : ℝ) ≤ ℓ ^ (4 : ℕ) := one_le_pow₀ hℓ1
    nlinarith
  -- the target width is tiny
  have hWsmall : (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hD4pos (by norm_num : (0:ℝ) < 2)]
    nlinarith
  by_cases hcase : Real.exp (Real.exp 100) + 1 ≤ |ρ.im|
  · -- ABOVE the floor: stones A+B
    have hβ1 : ρ.re < 1 := by
      by_contra hge
      exact LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (by linarith [not_lt.mp hge]) hρ0
    have hℓγ100 : (100 : ℝ) ≤ Real.log (Real.log |ρ.im|) := loglog_ge_hundred hcase
    have hgate : Real.log (20000 * (vkStripConst q + 8104))
        ≤ A * Real.log (Real.log |ρ.im|) := by
      have : A * 100 ≤ A * Real.log (Real.log |ρ.im|) :=
        mul_le_mul_of_nonneg_left hℓγ100 (by linarith)
      linarith
    -- the two arms deliver the same D₃-shaped width at the zero's own height
    have hstone : ρ.re ≤ 1 - (1 / (10 ^ 8 * (A + 7)))
        * (1 / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ))) := by
      by_cases hsq : ψ ^ 2 = 1
      · refine LFunction_real_zero_free_region_vk hψ1 hsq hA1 hρ0 hβ1 hcase ?_
        exact hgate
      · refine LFunction_zero_free_region_vk hψ1 hsq hA1 hρ0 hβ1 hcase ?_
        have hvk : (1 : ℝ) ≤ vkStripConst q := one_le_vkStripConst
        exact le_trans (Real.log_le_log (by linarith) (by linarith)) hgate
      -- (both arms take the SAME gate: `vkStripConst q ≤ vkStripConst q + 8104`)
    -- compare the two widths
    have hEexp1 : Real.exp 1 ≤ |ρ.im| := by
      have h1 : Real.exp 1 ≤ Real.exp (Real.exp 100) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hmono := logDn_mono 3 hEexp1 hρim
    have hDγpos : 0 < (Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ) := by
      have hL1 : (1 : ℝ) ≤ Real.log |ρ.im| := by
        have h := Real.log_le_log (Real.exp_pos 1) hEexp1; rwa [Real.log_exp] at h
      have h1 : 0 < (Real.log |ρ.im|) ^ ((3 : ℝ) / 4) :=
        Real.rpow_pos_of_pos (by linarith) _
      have h2 : 0 < (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ) := by positivity
      exact mul_pos h1 h2
    have hstep1 : (1 / (10 ^ 8 * (A + 7)) : ℝ) * (1 / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)))
        ≤ (1 / (10 ^ 8 * (A + 7)) : ℝ)
          * (1 / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact one_div_le_one_div_of_le hDγpos hmono
    have hstep2 : (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))
        ≤ (1 / (10 ^ 8 * (A + 7)) : ℝ) * (1 / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))) := by
      have hA7 : (0 : ℝ) < A + 7 := by linarith
      have hL : (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))
          = 1 / (10 ^ 8 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))) := by rw [div_div]
      have hR : (1 / (10 ^ 8 * (A + 7)) : ℝ) * (1 / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)))
          = 1 / (10 ^ 8 * (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))) := by
        rw [div_mul_div_comm, one_mul]
      have hden : (0 : ℝ) < 10 ^ 8 * (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)) :=
        mul_pos (mul_pos (by norm_num) hA7) hD3pos
      have hkey : (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))
          ≤ Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) := by
        calc (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))
            ≤ ℓ * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)) :=
              mul_le_mul_of_nonneg_right hAabs hD3pos.le
          _ = Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) := by ring
      rw [hL, hR]
      refine one_div_le_one_div_of_le hden ?_
      calc 10 ^ 8 * (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))
          = 10 ^ 8 * ((A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))) := by ring
        _ ≤ 10 ^ 8 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) := by linarith [hkey]
    linarith [hstone, hstep1, hstep2]
  · -- BELOW the floor: the classical effective region
    rw [not_le] at hcase
    rcases le_or_gt (1 / 2 : ℝ) ρ.re with hre | hre
    · by_cases him : ρ.im = 0
      · -- THE REAL-ZERO CORNER: §7's Siegel arm gives the conclusion outright
        have hW0 : (0 : ℝ) < (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) :=
          div_pos (by norm_num) hD4pos
        have hgate : (q : ℝ) ^ ((1 : ℝ) / 16)
            * ((1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))) ≤ Ks := by
          have heq : (q : ℝ) ^ ((1 : ℝ) / 16)
              * ((1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)))
              = ((q : ℝ) ^ ((1 : ℝ) / 16) * (1 / 10 ^ 8 : ℝ))
                / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) := by ring
          rw [heq, div_le_iff₀ hD4pos]
          nlinarith [hSg, hD4pos, hKs0]
        exact hsg q ψ hψ1 _ hW0 hgate ρ hρ0 him
      · have hcv : ψ.primitiveCharacter ^ 2 ≠ 1 ∨ ρ.im ≠ 0 := Or.inr him
        have hcl := hc₀ q ψ hψ1 hρ0 hre hcv
        have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
          have := Nat.pos_of_ne_zero (NeZero.ne q); exact_mod_cast this
        have hEq : |ρ.im| + 2 ≤ Real.exp (Real.exp 100) + 3 := by linarith
        have hlow0 : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
          apply Real.log_pos; nlinarith [abs_nonneg ρ.im]
        have hlowle : Real.log ((q : ℝ) * (|ρ.im| + 2))
            ≤ Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3)) := by
          apply Real.log_le_log (by nlinarith [abs_nonneg ρ.im])
          exact mul_le_mul_of_nonneg_left hEq (by linarith)
        have hlowE0 : 0 < Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3)) := by
          linarith
        -- the gate converts the fixed classical width into the VK-shaped one
        have hkey : (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))
            ≤ c₀ / Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3)) := by
          rw [div_le_div_iff₀ hD4pos hlowE0]
          have hgate' : Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
              ≤ 10 ^ 8 * c₀ * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) := by
            have h := hKq
            rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at h
            linarith
          nlinarith [hgate']
        have hshrink : c₀ / Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
          rw [div_le_div_iff₀ hlowE0 hlow0]
          exact mul_le_mul_of_nonneg_left hlowle hc₀0.le
        linarith [hcl, hkey, hshrink]
    · linarith [hWsmall, hre]

set_option maxHeartbeats 800000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open Complex MeasureTheory Set ArithmeticFunction DirichletCharacter in
open scoped LSeries.notation in
/-- **⟦Kq BOUNDED TWIN⟧** `halasz_primes_chi_pair_of_gates` + the conjunct `Kq ≤ 126848 / 10 ^ 8`.
the port's pair row; pass-through. -/
theorem halasz_primes_chi_pair_of_gates_bounded {C₁ C₂ C₃ T₀e : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃)
    (hT₀e : Real.exp (Real.exp 100) ≤ T₀e)
    (hprice : TwistedWindowPriceGated (1 / 10 ^ 8) C₁ C₂ C₃ T₀e) :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
        (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * Complex.I) * chiBarCoeff q r.1 a n‖ ^ 2
          ≤ C * (P + (ℰ.card : ℝ) * P
                  * Real.exp (-c * Real.log P
                      / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                          * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
                  * (Real.log ((q : ℝ) * T)) ^ 2)
              / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C, c, T₀, hC, hc, hT₀, hgated⟩ :=
    halaszPrimesChiGated_of_price (by norm_num) hC₁ hC₂ hC₃ hT₀e hprice
  obtain ⟨Kq, Ks, hKq, hKqb, hKs, hreg⟩ := twisted_rect_zero_free_siegel_bounded
  refine ⟨C, c, max T₀ T₀e, Kq, Ks, hC, hc, le_trans hT₀ (le_max_left _ _), hKq, hKqb, hKs, ?_⟩
  intro q hq T P hT hP hPT10 hG1 hG2 hG3 hG4 ℰ hws hsub S hS a
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hTfloor : Real.exp (Real.exp 100) ≤ T := le_trans hT₀e (le_trans (le_max_right _ _) hT)
  -- the `A`-instantiation that makes stone C's own `hAq` free
  set A : ℝ := 1 + Real.log (20000 * (vkStripConst q + 8104)) / 100 with hAdef
  have hCq1 : (1 : ℝ) ≤ vkStripConst q := one_le_vkStripConst
  have hlogA0 : (0 : ℝ) ≤ Real.log (20000 * (vkStripConst q + 8104)) :=
    Real.log_nonneg (by linarith)
  have hA1 : (1 : ℝ) ≤ A := by rw [hAdef]; linarith
  have hAq : Real.log (20000 * (vkStripConst q + 8104)) ≤ A * 100 := by
    rw [hAdef]; linarith
  have hAabs : A + 7 ≤ Real.log (Real.log (5 * T + 1)) := by rw [hAdef]; linarith [hG2]
  exact hgated q T P hTT₀ hP hPT10 hG1
    (fun ψ hψ1 => hreg q ψ hψ1 A T hA1 hTfloor hAq hAabs hG3 hG4) ℰ hws hsub S hS a

set_option maxHeartbeats 800000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open Complex DirichletCharacter in
/-- **⟦Kq BOUNDED TWIN⟧** `halaszPrimesChi_holds_gated` + the conjunct `Kq ≤ 126848 / 10 ^ 8`.
the gated socket row; pass-through. -/
theorem halaszPrimesChi_holds_gated_bounded :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
        (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * Complex.I) * chiBarCoeff q r.1 a n‖ ^ 2
          ≤ C * (P + (ℰ.card : ℝ) * P
                  * Real.exp (-c * Real.log P
                      / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                          * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
                  * (Real.log ((q : ℝ) * T)) ^ 2)
              / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C₁, C₂, C₃, T₀e, hC₁, hC₂, hC₃, hT₀e, hprice⟩ := twisted_window_price_gated_holds
  exact halasz_primes_chi_pair_of_gates_bounded hC₁ hC₂ hC₃ hT₀e hprice

set_option maxHeartbeats 800000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open Complex DirichletCharacter in
/-- **⟦Kq BOUNDED TWIN⟧** `halaszPrimesChi_pointwise_of_gates` + the conjunct `Kq ≤ 126848 / 10 ^ 8`.
the pointwise socket; pass-through. -/
theorem halaszPrimesChi_pointwise_of_gates_bounded :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T : ℝ), T₀ ≤ T →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      HalaszPrimesChi C c q T := by
  obtain ⟨C, c, T₀, Kq, Ks, hC, hc, hT₀, hKq, hKqb, hKs, hrow⟩ := halaszPrimesChi_holds_gated_bounded
  refine ⟨C, c, T₀, Kq, Ks, hC, hc, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ T hT hG1 hG2 hG3 hG4 P hP hPT10 ℰ hws hsub S hS a
  exact hrow q T P hT hP hPT10 hG1 hG2 hG3 hG4 ℰ hws hsub S hS a

set_option maxHeartbeats 1200000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open MeasureTheory in
/-- **⟦Kq BOUNDED TWIN⟧** `usetGChi_window_meansq_gated_family_perBlock` + the conjunct `Kq ≤ 126848 / 10 ^ 8`.
the χ-summed window mean square, gated; pass-through. -/
theorem usetGChi_window_meansq_gated_family_perBlock_bounded :
    ∃ Cs cs T₀ Kq Ks : ℝ, 0 < Cs ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (f : ℕ → ℂ), (∀ n : ℕ, ‖f n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (T VJ V L X : ℝ), 1 ≤ T → 1 < (q : ℝ) * T →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T →
        30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * T)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → T ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        -- ⟦THE PER-`(q,T)` FLOOR — what the socket's discharge costs⟧
        T₀ ≤ T →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * T) → Real.log ((q : ℝ) * T) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ),
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q,
          thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, H ≤ (j : ℝ)) →
        (∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * T) →
        (∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * T) / Real.log (ramQbase H P j)) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ T ^ 10) →
        (∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L) →
        (∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase H P j)) ^ 2) →
      ∀ Rbd : ℝ, 0 ≤ Rbd →
      ∀ 𝔄 : Set (DirichletCharacter ℂ q × ℝ),
        (∀ χ : DirichletCharacter ℂ q, MeasurableSet {t : ℝ | (χ, t) ∈ 𝔄}) →
        (∀ r ∈ 𝔄, r.2 ∈ Set.Icc (-T) T) →
        𝔄 ⊆ UsetGChi q f Pseq Qseq Hseq αseq J →
        (∀ j ∈ ramI H P Q, ∀ r ∈ 𝔄,
          ‖ramR H N Xd P Q j (chiBarCoeff q r.1 b) r.2‖ ≤ Rbd) →
      ∀ E : ℝ, (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
          ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
        (∑ χ : DirichletCharacter ℂ q,
            ∫ t in {t : ℝ | (χ, t) ∈ 𝔄}, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (∑ j ∈ ramI H P Q,
                  (5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ)
                        * (1 + Real.log (2 * T))
                      * (∑ m ∈ Finset.Icc 1 (Ms j),
                          ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
                    + 81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2))
            + 2 * E := by
  obtain ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hT₀, hKq, hKqb, hKs, hpt⟩ :=
    halaszPrimesChi_pointwise_of_gates_bounded
  refine ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 T VJ V L X hT1 hqT hP3 hPQ
    hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL
    hgate Rbd hRbd 𝔄 hAm hAsub hUA hR E herr
  exact usetGChi_window_meansq_of_socket_family_perBlock hCs hcs q f hf1 Pseq Qseq Hseq αseq
    J Jb hJb1 hJbJ hH2seq hα0 T VJ V L X (hpt q T hT₀T hG1 hG2 hG3 hG4) hT1 hqT hP3 hPQ hQT
    hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hlogT1 hTL hLe hlogV
    H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate Rbd hRbd
    𝔄 hAm hAsub hUA hR E herr

set_option maxHeartbeats 1200000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open MeasureTheory in
/-- **⟦Kq BOUNDED TWIN⟧** `usetGChi_row_exit_perChi_perBlock` + the conjunct `Kq ≤ 126848 / 10 ^ 8`.
the per-χ row exit; pass-through (only `Cs` rescales). -/
theorem usetGChi_row_exit_perChi_perBlock_bounded :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (Tann VJ V L X : ℝ), 1 ≤ Tann → 1 < (q : ℝ) * Tann →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann →
        30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * Tann)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → Tann ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        T₀ ≤ Tann →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * Tann + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * Tann) → Real.log ((q : ℝ) * Tann) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ),
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q,
          thinBundleGChi ((q : ℝ) * Tann) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, H ≤ (j : ℝ)) →
        (∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * Tann) →
        (∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * Tann) / Real.log (ramQbase H P j)) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ Tann ^ 10) →
        (∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L) →
        (∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase H P j)) ^ 2) →
      ∀ Rbd : ℝ, 0 ≤ Rbd →
      ∀ t₁ : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ j ∈ ramI H P Q,
          ∀ t ∈ seamAnn X Tann \ seamBall X (t₁ χ),
            ‖ramR H N Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd) →
      ∀ E : ℝ, (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
          ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
      ∀ KS : ℝ,
        (∀ j ∈ ramI H P Q,
          5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
              * (∑ m ∈ Finset.Icc 1 (Ms j),
                  ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
            ≤ KS) →
        2 ≤ ⌊H * Real.log (P : ℝ)⌋₊ →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (seamAnn X Tann \ seamBall X (t₁ χ))
            ∩ UsetG (chiBarCoeff q χ c) Pseq Qseq Hseq αseq J,
            ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (((ramI H P Q).card : ℝ) * KS
                  + 54 * Cq * Rbd ^ 2 * H ^ 2
                      / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E := by
  obtain ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hT₀, hKq, hKqb, hKs, hfam⟩ :=
    usetGChi_window_meansq_gated_family_perBlock_bounded
  refine ⟨3 * Cs / 2, cs, T₀, Kq, Ks, by linarith, hcs, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X hT1 hqT hP3
    hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL
    hgate Rbd hRbd t₁ hR E herr KS hKS hj₀ χ
  -- ⟦the Σ_χ exit at the row's own pair set⟧
  have hsum := hfam q c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X
    hT1 hqT hP3 hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T
    hG1 hG2 hG3 hG4 hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3
    hBT hκ30 hBT10 hWL hgate Rbd hRbd
    (rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁)
    (measurableSet_rowPairSetG_fibre q c Pseq Qseq Hseq αseq J X Tann t₁)
    (rowPairSetG_sub q c Pseq Qseq Hseq αseq J X Tann t₁)
    (rowPairSetG_subset_UsetGChi q c Pseq Qseq Hseq αseq J X Tann t₁)
    (fun j hj r hr => hR r.1 j hj r.2 hr.1) E herr
  -- ⟦the per-χ read: every fibre integral is nonnegative, so one is at most the sum⟧
  have hnn : ∀ χ' ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      (0 : ℝ) ≤ ∫ t in {t : ℝ | (χ', t) ∈ rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁},
        ‖spoly N (chiBarCoeff q χ' a) t‖ ^ 2 := by
    intro χ' _
    exact setIntegral_nonneg
      (measurableSet_rowPairSetG_fibre q c Pseq Qseq Hseq αseq J X Tann t₁ χ')
      (fun _ _ => by positivity)
  have hsingle := Finset.single_le_sum hnn (Finset.mem_univ χ)
  -- ⟦the ⟦ii-8⟧ block price, per block⟧
  have hprice := usetGChi_block_price_perBlock H N Xd P Q Ms b X Tann KS Cs Rbd hCs.le hRbd
    hj₀ hKS
  have hcard0 : (0 : ℝ) ≤ 4 * ((ramI H P Q).card : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hprice hcard0
  rw [rowPairSetG_fibre] at hsingle
  linarith

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open MeasureTheory in
/-- **⟦Kq BOUNDED TWIN⟧** `m4_rowChi_capstone_perBlock` + the conjunct `Kq ≤ 126848 / 10 ^ 8`.
the per-χ capstone row, per block; pass-through. -/
theorem m4_rowChi_capstone_perBlock_bounded :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (Tann VJ V L X : ℝ), 1 ≤ Tann → 1 < (q : ℝ) * Tann →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann →
        30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * Tann)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → Tann ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        T₀ ≤ Tann →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * Tann + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * Tann) → Real.log ((q : ℝ) * Tann) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
        -- ⟦THE `X`-SIDE FRAME⟧
        2 ≤ H83 X theta293 → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann →
      ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleGChi ((q : ℝ) * Tann) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, H83 X theta293 ≤ (j : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 3 ≤ ramQbase (H83 X theta293) P j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          (ramQbase (H83 X theta293) P j : ℝ) ≤ (q : ℝ) * Tann) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          30 ≤ Real.log ((q : ℝ) * Tann) / Real.log (ramQbase (H83 X theta293) P j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          (ramQbase (H83 X theta293) P j : ℝ) ≤ Tann ^ 10) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          Real.log (ramQbase (H83 X theta293) P j) ≤ L) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase (H83 X theta293) P j)) ^ 2) →
      ∀ (Rbd CR : ℝ), 0 ≤ Rbd → Rbd ≤ CR * (Real.log X) ^ (-rho293) →
        1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
      ∀ t₁ : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ j ∈ ramI (H83 X theta293) P Q,
          ∀ t ∈ seamAnn X Tann \ seamBall X (t₁ χ),
            ‖ramR (H83 X theta293) N Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd) →
      ∀ KS : ℝ, 0 ≤ KS →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
              * (∑ m ∈ Finset.Icc 1 (Ms j),
                  ‖ramRcoeff (H83 X theta293) N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
            ≤ KS) →
        32 * (Real.log X) ^ (2 + 2 * theta293) * KS ≤ (Real.log X) ^ (-theta293) →
      ∀ (E EP2 εr : ℝ), 0 ≤ εr → 8640 ≤ (Real.log X) ^ εr →
        12 * EP2 ≤ (Real.log X) ^ (-theta293 + εr) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
          ‖ramErr (H83 X theta293) N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
      ∀ S : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann →
          |t - t₁ χ| ≤ seamRad X → ∀ m : ℕ, m ≤ N →
            ‖spolyA (chiBarCoeff q χ a) t m‖ ≤ S χ * m / (1 + |t - t₁ χ|)) →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 8 * S χ ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X (t₁ χ))
                ∩ seamTtotG (chiBarCoeff q χ c) Pseq Qseq Hseq αseq J,
                ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + εr)) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKqb, hKs, hexit⟩ :=
    usetGChi_row_exit_perChi_perBlock_bounded
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X hT1 hqT hP3
    hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV hH2 hLXe hL4 hTgate
    N Xd P Q Ms a b cf hcf1 hPlow hQ0 hQhigh hM hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate
    Rbd CR hRbd hRgrade hCqgate t₁ hR KS hKS0 hKS hKSgate E EP2 εr hεr habs hEP2 hErow herr
    hXN hN2 hsupp S hSup χ
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hH0 : (0 : ℝ) ≤ H83 X theta293 := by linarith
  have hHeq : H83 X theta293 = (Real.log X) ^ theta293 := by rw [H83]
  have hTann0 : (0 : ℝ) ≤ Tann := by linarith
  have hfl := floor_pin X P hL4 hPlow
  -- ⟦the per-χ `𝒰` exit, per block⟧
  have hU := hexit q c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X
    hT1 hqT hP3 hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T
    hG1 hG2 hG3 hG4 hlogT1 hTL hLe hlogV (H83 X theta293) hH2 N Xd P Q Ms a b cf hcf1 hM
    hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate Rbd hRbd t₁ hR E herr KS hKS hfl.1 χ
  -- ⟦the block leg, priced at `θ₂₉₃`⟧
  have hmain := balance_priced_main X (H83 X theta293) Cq CR KS Rbd P Q hL0 hH0
    (ramI_card_le_pin X P Q hQ0 hQhigh hLXe) (le_of_eq hHeq) hfl.2
    hCq.le hKS0 hRbd hRgrade hKSgate hCqgate
  -- ⟦Lemma 12's error leg, absorbed⟧
  have hrem := rem_priced X Tann (H83 X theta293) εr EP2 E hL1 hX0 hTann0
    (le_of_eq hHeq.symm) habs hEP2 hErow
  -- ⟦the balance⟧
  have hbal := hUG_balance (chiBarCoeff q χ a) (chiBarCoeff q χ c) N Pseq Qseq Hseq αseq J
    X Tann (t₁ χ) εr _ _ hεr hL1 hX0 hTgate hU hmain hrem
  exact prop_A3_T1_row_split_weightedG (chiBarCoeff q χ a) N (chiBarCoeff q χ c) Pseq Qseq
    Hseq αseq J X Tann (t₁ χ) (S χ) _ hL0.le hTann0 hX0 hXN hN2
    (chiBarCoeff_seam_supp χ hsupp) (hSup χ) hbal

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open MeasureTheory in
open Salt.Entropy.Chowla in
/-- **⟦Kq BOUNDED TWIN⟧** `m4_hcap_at_door_perBlock_gk` + the conjunct `Kq ≤ 126848 / 10 ^ 8`.
the cap wire at the door, per block; pass-through. -/
theorem m4_hcap_at_door_perBlock_gk_bounded (K : ℕ) :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 : ℝ),
              DoorCapBasePerBlock_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf (2 * T)
                VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2) →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKqb, hKs, hcapstone⟩ := m4_rowChi_capstone_perBlock_bounded
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKqb, hKs, ?_⟩
  intro R M cU ε hcU hfam H L q j A s hb χ T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, hd⟩ :=
    hfam H L q j A s hb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hlogX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := hd.logX_four
    linarith
  have hres := hcapstone q cU hcU (calP (Adoor M) (s13GK K M))
    (calQK (Adoor M) (s13GK K M) M) (calH (H1door M)) (mrAlpha (1 / 12)) 2 Jb
    hd.Jb_lo hd.Jb_hi hd.Hseq_two hd.alpha_nonneg
    (2 * T) VJ V Lr (((A + s : ℕ)) : ℝ) hd.Tann_one hd.qTann_one hd.P_three hd.PQ hd.QTann
    hd.kappa30Q hd.loglog5 hd.VJ_bound η εd hd.alpha_eta hd.eta_half hd.Tann_X hd.X_pos
    hd.debit hd.logX_pos hd.q_logX hd.V_one hd.V_inv hd.T0_Tann hd.floor1 hd.floor2
    hd.floor3 hd.floor4 hd.logqT_one hd.logqT_L hd.L_exp hd.logV_L
    hd.H83_two hd.logX_exp hd.logX_four hTgate
    (2 * (A + s)) Xd P Q Mr (winCutH (A + s) (doorCoeffU_gk K M)) b cf hd.cf_one hd.P_low
    hd.Q_pos hd.Q_high hd.range hd.budget hd.Hj hd.B3 hd.BT hd.kappa30 hd.BT10 hd.WL hd.gate
    Rbd CR hd.Rbd_nonneg hd.Rbd_grade hd.Cq_gate
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ)) hd.Rbd_binder
    KS hd.KS_nonneg hd.KS_binder hd.KS_gate E EP2 (ε (A + s)) hd.epsr_nonneg hd.abs8640
    hd.EP2_gate hd.E_row hd.E_binder (doorCap_hXN (A + s)) (doorCap_hN2 (A + s))
    (fun n hn => doorRowDatumU_supp0_gk K M (A + s) hn)
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ))
    (m4_hSup_door_at_zero q (winCutH (A + s) (doorCoeffU_gk K M)) (2 * (A + s)) hlogX1) χ
  rw [chiBarCoeff_doorRowDatum_gk] at hres
  simpa using hres

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open MeasureTheory in
open Salt.Entropy.Chowla in
/-- **⟦Kq BOUNDED TWIN⟧** `m4_fuse_hcap_of_capWS_gk` + the conjunct `Kq ≤ 126848 / 10 ^ 8`.
⟦THE TOP UNFENCED HOP OF ROUTE 3⟧ — the cap-wire fuse `S16Uniform` :660 opens. -/
theorem m4_fuse_hcap_of_capWS_gk_bounded (K : ℕ) :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
              DoorCapErrWS_gk K M (A + s) q Xd P Q b cf (2 * T) E Mtail
                ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                      ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                        (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU_gk K M)))
                        (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                    → DoorCapBasePerBlock_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                        (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKqb, hKs, hwire⟩ := m4_hcap_at_door_perBlock_gk_bounded K
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKqb, hKs, ?_⟩
  intro R M cU ε hc1 hcapWS
  refine hwire R M cU ε hc1 ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (m4_capE_at_door_gk K hws)⟩

/-! ## §14 — the ceiling in the terminal's own shape -/

/-- `126848/10^8 ≤ e^100` — forty-six orders of room. -/
theorem kq_closed_form_le_exp_hundred : (126848 : ℝ) / 10 ^ 8 ≤ Real.exp 100 := by
  have h : (1 : ℝ) ≤ Real.exp 100 := by
    have := Real.add_one_le_exp (100 : ℝ); linarith
  linarith

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open MeasureTheory in
open Salt.Entropy.Chowla in
/-- **⟦THE COMPOSE HOOK OF ROUTE 3⟧** — `m4_fuse_hcap_of_capWS_gk_bounded`
with the ceiling stated in the terminal's own numeral `e^100`. -/
theorem m4_fuse_hcap_of_capWS_gk_ceiling (K : ℕ) :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ Kq ≤ Real.exp 100 ∧ 0 < Ks ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
              DoorCapErrWS_gk K M (A + s) q Xd P Q b cf (2 * T) E Mtail
                ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                      ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                        (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU_gk K M)))
                        (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                    → DoorCapBasePerBlock_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                        (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKqb, hKs, hwire⟩ :=
    m4_fuse_hcap_of_capWS_gk_bounded K
  exact ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq,
    le_trans hKqb kq_closed_form_le_exp_hundred, hKs, hwire⟩

end Salt.MR

end
