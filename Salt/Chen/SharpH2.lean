/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.SharpH

/-!
# E₁c-hh2 — the IBP pushforward core (`hpush`) + the flat cell

Completes the sharp `h`-comparison begun in `SharpH.lean`.  The measure control
(`upset_mass_le`) and the `S ≥ 2` cell scaffold (`hh_sharp_ge2_of_pushforward`) are landed there;
this file supplies the missing analytic engine: the honest discrete → integral pushforward
`hpush`, via the layer-cake / integration-by-parts identity against the antitone `hBJS`.

## The engine

Write `Kh := -hBJS'` — the (nonnegative) descending-`V` kernel:
`Kh v = 0` on `v ≤ 2`, `e^{-v}` on `(2,3]`, `3(v⁻¹+v⁻²)e^{-v}` on `v > 3`.
The master IBP lemma `hBJS_ibp_master` proves, for any `C¹` weight `φ`,
`∫_a^b (φ' hBJS - φ Kh) = φ(b)hBJS(b) - φ(a)hBJS(a)` (FTC-2 on the three smooth branches of
`hBJS`, glued at the kinks `2, 3`).  Two instances:
* `φ = 1`:  the FTC `∫_a^b Kh = hBJS a - hBJS b`;
* `φ = B`, `B(v) = (1+ε)(v+1)/S - 1`:  the integration by parts that converts the affine mass
  bound `upset_mass_le` into `ε·hBJS(S-1) + (1+ε)(1/S)∫ hBJS`.

The discrete sum is reconstructed against the integral by a `Finset.induction` (the "layer cake",
`hpush_identity`), using the single-prime indicator identity — this avoids the full Fubini
`integral_finset_sum` machinery.
-/

open Finset MeasureTheory intervalIntegral Set

namespace Salt.Chen

/-! ## Part 0 — the kernel `Kh = -hBJS'` and its integrability -/

/-- `Kh = -hBJS'`, the nonnegative descending-`V` kernel: `0` on `v ≤ 2`, `e^{-v}` on `(2,3]`,
`3(v⁻¹+v⁻²)e^{-v}` on `v > 3`.  (Values at the kinks `2, 3` are irrelevant — measure zero.) -/
noncomputable def Kh (v : ℝ) : ℝ :=
  if v ≤ 2 then 0 else if v ≤ 3 then Real.exp (-v) else 3 * (v⁻¹ + v⁻¹ ^ 2) * Real.exp (-v)

theorem Kh_nonneg (v : ℝ) : 0 ≤ Kh v := by
  unfold Kh
  split_ifs with h1 h2
  · exact le_rfl
  · exact (Real.exp_pos _).le
  · have hv : (0 : ℝ) < v := lt_trans (by norm_num) (not_le.mp h2)
    have hi : (0 : ℝ) < v⁻¹ := inv_pos.mpr hv
    positivity

/-- `Kh ≤ (4/3)·hBJS` globally: equal on `(2,3]`, `≤` on the tail (`3(v⁻¹+v⁻²) ≤ 4v⁻¹ ⟺ v ≥ 3`). -/
theorem Kh_le (v : ℝ) : Kh v ≤ (4 / 3) * hBJS v := by
  unfold Kh hBJS
  split_ifs with h1 h2
  · have := Real.exp_pos (-2 : ℝ); nlinarith
  · have := Real.exp_pos (-v); nlinarith
  · have hv : (3 : ℝ) < v := not_le.mp h2
    have hi : (0 : ℝ) < v⁻¹ := inv_pos.mpr (by linarith)
    have he : (0 : ℝ) < Real.exp (-v) := Real.exp_pos _
    have hvv : v⁻¹ * v = 1 := inv_mul_cancel₀ (by linarith)
    -- need 3(v⁻¹+v⁻²)e ≤ (4/3)(3 v⁻¹ e) = 4 v⁻¹ e, i.e. 3 v⁻² ≤ v⁻¹, i.e. 3 v⁻¹ ≤ 1
    have hkey : 3 * v⁻¹ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right (le_of_lt hv) hi.le
      rw [mul_comm v v⁻¹, hvv] at h; exact h
    nlinarith [mul_le_mul_of_nonneg_right hkey hi.le, he, mul_pos hi he]

theorem Kh_measurable : Measurable Kh := by
  unfold Kh
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_le measurable_id measurable_const)
    (Real.measurable_exp.comp measurable_neg) ?_
  exact (measurable_const.mul (measurable_inv.add (measurable_inv.pow_const 2))).mul
    (Real.measurable_exp.comp measurable_neg)

/-- `Kh` is interval integrable on every interval (measurable and bounded by `(4/3)e^{-2}`). -/
theorem Kh_intervalIntegrable (a b : ℝ) : IntervalIntegrable Kh volume a b := by
  rw [intervalIntegrable_iff]
  apply MeasureTheory.Measure.integrableOn_of_bounded (M := (4 / 3) * Real.exp (-2)) _
    Kh_measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Kh_nonneg s)]
      calc Kh s ≤ (4 / 3) * hBJS s := Kh_le s
        _ ≤ (4 / 3) * Real.exp (-2) := by nlinarith [hBJS_le_exp2 s, Real.exp_pos (-2 : ℝ)]))
  rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top

/-! ## Part 1 — the branch derivatives of `hBJS` -/

/-- `d/dv e^{-v} = -e^{-v}`. -/
theorem hasDerivAt_expNeg (x : ℝ) : HasDerivAt (fun v : ℝ => Real.exp (-v)) (-Real.exp (-x)) x := by
  have h0 : HasDerivAt (fun v : ℝ => -v) (-1 : ℝ) x := (hasDerivAt_id x).neg
  have h1 : HasDerivAt (fun v : ℝ => Real.exp (-v)) (Real.exp (-x) * (-1)) x :=
    (Real.hasDerivAt_exp (-x)).comp x h0
  simpa using h1

/-- `d/dv (3 v⁻¹ e^{-v}) = -(3(v⁻¹+v⁻²)e^{-v})` for `v ≠ 0`. -/
theorem hasDerivAt_tailFn {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun v : ℝ => 3 * v⁻¹ * Real.exp (-v))
      (-(3 * (x⁻¹ + x⁻¹ ^ 2) * Real.exp (-x))) x := by
  have hexp := hasDerivAt_expNeg x
  have hinv : HasDerivAt (fun v : ℝ => v⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx
  have hmul := (hinv.const_mul (3 : ℝ)).mul hexp
  have hEq : (3 : ℝ) * (-(x ^ 2)⁻¹) * Real.exp (-x) + 3 * x⁻¹ * -Real.exp (-x)
      = -(3 * (x⁻¹ + x⁻¹ ^ 2) * Real.exp (-x)) := by
    rw [← inv_pow]; ring
  rw [← hEq]; exact hmul

/-! ## Part 2 — the master IBP engine `∫ (φ' hBJS - φ Kh) = φ·hBJS |ᵇₐ` -/

/-- The single-branch IBP: on a closed interval `[a,b]` where `hBJS = bf` and `Kh = -bf'`
(with `bf` smooth), `∫_a^b (φ' hBJS - φ Kh) = φ(b)hBJS(b) - φ(a)hBJS(a)`.  FTC-2 applied to the
smooth antiderivative `φ·bf`. -/
theorem ibp_on (φ φ' bf bf' : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ'c : Continuous φ') (a b : ℝ) (hab : a ≤ b)
    (hbf : ∀ x ∈ Set.Ioo a b, HasDerivAt bf (bf' x) x)
    (hbfc : ContinuousOn bf (Set.Icc a b))
    (hEqBJS : ∀ x ∈ Set.Icc a b, hBJS x = bf x)
    (hEqK : ∀ x ∈ Set.Ioo a b, Kh x = -bf' x) :
    ∫ v in a..b, (φ' v * hBJS v - φ v * Kh v) = φ b * hBJS b - φ a * hBJS a := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 (fun x => (hφ x).continuousAt)
  have hcontG : ContinuousOn (fun v => φ v * bf v) (Set.Icc a b) := hφc.continuousOn.mul hbfc
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun v => φ v * bf v) (φ' x * hBJS x - φ x * Kh x) x := by
    intro x hx
    have hmul := (hφ x).mul (hbf x hx)
    have hD : φ' x * hBJS x - φ x * Kh x = φ' x * bf x + φ x * bf' x := by
      rw [hEqBJS x (Set.Ioo_subset_Icc_self hx), hEqK x hx]; ring
    rw [hD]; exact hmul
  have hint : IntervalIntegrable (fun v => φ' v * hBJS v - φ v * Kh v) volume a b :=
    ((hBJS_intervalIntegrable a b).continuousOn_mul hφ'c.continuousOn).sub
      ((Kh_intervalIntegrable a b).continuousOn_mul hφc.continuousOn)
  have hres := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcontG hderiv hint
  rw [hres, ← hEqBJS a (Set.left_mem_Icc.mpr hab), ← hEqBJS b (Set.right_mem_Icc.mpr hab)]

/-- **The master IBP engine.**  For any `C¹` weight `φ` (derivative `φ'` continuous),
`∫_a^b (φ' hBJS - φ Kh) = φ(b)hBJS(b) - φ(a)hBJS(a)`.  Glues `ibp_on` over the three branches of
`hBJS` at the kinks `2, 3`. -/
theorem hBJS_ibp_master (φ φ' : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ'c : Continuous φ') (a b : ℝ) (hab : a ≤ b) :
    ∫ v in a..b, (φ' v * hBJS v - φ v * Kh v) = φ b * hBJS b - φ a * hBJS a := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 (fun x => (hφ x).continuousAt)
  have hII : ∀ p q : ℝ,
      IntervalIntegrable (fun v => φ' v * hBJS v - φ v * Kh v) volume p q := fun p q =>
    ((hBJS_intervalIntegrable p q).continuousOn_mul hφ'c.continuousOn).sub
      ((Kh_intervalIntegrable p q).continuousOn_mul hφc.continuousOn)
  -- the three smooth branches
  have flat : ∀ p q : ℝ, p ≤ q → q ≤ 2 →
      (∫ v in p..q, (φ' v * hBJS v - φ v * Kh v)) = φ q * hBJS q - φ p * hBJS p := by
    intro p q hpq hq2
    apply ibp_on φ φ' (fun _ => Real.exp (-2)) (fun _ => 0) hφ hφ'c p q hpq
    · intro x _; exact hasDerivAt_const x _
    · exact continuousOn_const
    · intro x hx; exact hBJS_le2 (le_trans hx.2 hq2)
    · intro x hx; rw [neg_zero]; unfold Kh
      rw [if_pos (le_of_lt (lt_of_lt_of_le hx.2 hq2))]
  have mid : ∀ p q : ℝ, 2 ≤ p → p ≤ q → q ≤ 3 →
      (∫ v in p..q, (φ' v * hBJS v - φ v * Kh v)) = φ q * hBJS q - φ p * hBJS p := by
    intro p q hp2 hpq hq3
    apply ibp_on φ φ' (fun v => Real.exp (-v)) (fun v => -Real.exp (-v)) hφ hφ'c p q hpq
    · intro x _; exact hasDerivAt_expNeg x
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
    · intro x hx; exact hBJS_mid (le_trans hp2 hx.1) (le_trans hx.2 hq3)
    · intro x hx; rw [neg_neg]; unfold Kh
      rw [if_neg (not_le.mpr (lt_of_le_of_lt hp2 hx.1)),
        if_pos (le_of_lt (lt_of_lt_of_le hx.2 hq3))]
  have tail : ∀ p q : ℝ, 3 ≤ p → p ≤ q →
      (∫ v in p..q, (φ' v * hBJS v - φ v * Kh v)) = φ q * hBJS q - φ p * hBJS p := by
    intro p q hp3 hpq
    have hppos : ∀ x ∈ Set.Icc p q, x ≠ 0 := fun x hx =>
      (lt_of_lt_of_le (by linarith : (0:ℝ) < p) hx.1).ne'
    apply ibp_on φ φ' (fun v => 3 * v⁻¹ * Real.exp (-v))
      (fun v => -(3 * (v⁻¹ + v⁻¹ ^ 2) * Real.exp (-v))) hφ hφ'c p q hpq
    · intro x hx; exact hasDerivAt_tailFn (lt_trans (by linarith : (0:ℝ) < p) hx.1).ne'
    · exact ((continuousOn_const.mul
        (continuousOn_id.inv₀ hppos)).mul (Real.continuous_exp.comp continuous_neg).continuousOn)
    · intro x hx; exact hBJS_ge3 (le_trans hp3 hx.1)
    · intro x hx; rw [neg_neg]; unfold Kh
      rw [if_neg (not_le.mpr (by linarith [hx.1] : (2:ℝ) < x)),
        if_neg (not_le.mpr (by linarith [hx.1] : (3:ℝ) < x))]
  -- glue by the position of the kinks 2, 3
  rcases le_total b 2 with hb2 | hb2
  · exact flat a b hab hb2
  · rcases le_total a 2 with ha2 | ha2
    · rcases le_total b 3 with hb3 | hb3
      · rw [← integral_add_adjacent_intervals (hII a 2) (hII 2 b),
          flat a 2 ha2 le_rfl, mid 2 b le_rfl hb2 hb3]; ring
      · rw [← integral_add_adjacent_intervals (hII a 2) (hII 2 b),
          ← integral_add_adjacent_intervals (hII 2 3) (hII 3 b),
          flat a 2 ha2 le_rfl, mid 2 3 le_rfl (by norm_num) le_rfl, tail 3 b le_rfl hb3]; ring
    · rcases le_total b 3 with hb3 | hb3
      · exact mid a b ha2 hab hb3
      · rcases le_total a 3 with ha3 | ha3
        · rw [← integral_add_adjacent_intervals (hII a 3) (hII 3 b),
            mid a 3 ha2 ha3 le_rfl, tail 3 b le_rfl hb3]; ring
        · exact tail a b ha3 hab

/-- **FTC for `hBJS`.**  `∫_a^b Kh = hBJS a - hBJS b` (`φ = 1` in the master engine). -/
theorem hBJS_ftc (a b : ℝ) (hab : a ≤ b) :
    ∫ v in a..b, Kh v = hBJS a - hBJS b := by
  have hm := hBJS_ibp_master (fun _ => 1) (fun _ => 0)
    (fun x => hasDerivAt_const x 1) continuous_const a b hab
  simp only [zero_mul, one_mul, zero_sub] at hm
  rw [intervalIntegral.integral_neg] at hm
  linarith [hm]

/-! ## Part 3 — the single-prime indicator identity and the layer-cake pushforward -/

/-- `fun v => if y ≤ v then Kh v else 0` is interval integrable (dominated by `Kh`). -/
theorem Kh_indicator_intervalIntegrable (y a b : ℝ) :
    IntervalIntegrable (fun v => if y ≤ v then Kh v else 0) volume a b := by
  have hmeas : Measurable (fun v => if y ≤ v then Kh v else 0) :=
    Measurable.ite (measurableSet_le measurable_const measurable_id) Kh_measurable measurable_const
  apply (Kh_intervalIntegrable a b).mono_fun' hmeas.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖(if y ≤ x then Kh x else 0)‖ ≤ Kh x
  have hnn : (0 : ℝ) ≤ (if y ≤ x then Kh x else 0) := by
    split_ifs with h
    · exact Kh_nonneg x
    · exact le_rfl
  rw [Real.norm_of_nonneg hnn]
  split_ifs with h
  · exact le_rfl
  · exact Kh_nonneg x

/-- **The single-prime indicator identity.**  For `a ≤ y ≤ b`,
`∫_a^b (if y ≤ v then Kh v else 0) = ∫_y^b Kh`.  (The `[a,y)` part is null; the `[y,b]` part is
`Kh`.) -/
theorem prime_indicator_integral (y a b : ℝ) (h1 : a ≤ y) (h2 : y ≤ b) :
    (∫ v in a..b, (if y ≤ v then Kh v else 0)) = ∫ v in y..b, Kh v := by
  have hlo : (∫ v in a..y, (if y ≤ v then Kh v else 0)) = 0 := by
    rw [show (0 : ℝ) = ∫ _v in a..y, (0 : ℝ) from by simp]
    apply intervalIntegral.integral_congr_ae
    have hy_ne : ∀ᵐ v : ℝ, v ≠ y := by
      rw [MeasureTheory.ae_iff]
      simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
    filter_upwards [hy_ne] with v hv hmem
    rw [Set.uIoc_of_le h1] at hmem
    have hlt : ¬ y ≤ v := not_le.mpr (lt_of_le_of_ne hmem.2 hv)
    simp [if_neg hlt]
  have hhi : (∫ v in y..b, (if y ≤ v then Kh v else 0)) = ∫ v in y..b, Kh v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le h2] at hv
    exact if_pos hv.1
  have hsplit : (∫ v in a..b, (if y ≤ v then Kh v else 0))
      = (∫ v in a..y, (if y ≤ v then Kh v else 0))
        + ∫ v in y..b, (if y ≤ v then Kh v else 0) :=
    (integral_add_adjacent_intervals (Kh_indicator_intervalIntegrable y a y)
      (Kh_indicator_intervalIntegrable y y b)).symm
  rw [hsplit, hlo, hhi, zero_add]

/-! ## Part 4 — the generic layer-cake pushforward -/

/-- **The generic layer-cake pushforward.**  For nonnegative Stieltjes masses `m p` sitting at
points `xp p ∈ [S-1, U]`, with the affine up-set mass control `hmass`
(`Σ_{xp p ≤ v} m p ≤ ((1+ε)(v+1)/S - 1)·W`), the antitone `hBJS`-weighted sum is bounded by the
integrated form.  This is `hpush` stripped of the number theory: the FTC (`hBJS_ftc`), the
finite sum↔integral swap (`integral_finsetSum` + `prime_indicator_integral`), monotonicity, and the
integration by parts (`hBJS_ibp_master`). -/
theorem layer_cake_pushforward (m xp : ℕ → ℝ) (win : Finset ℕ) (W S U ε : ℝ)
    (_hW : 0 < W) (hS : 0 < S) (hSU : S - 1 ≤ U)
    (_hm : ∀ p ∈ win, 0 ≤ m p)
    (hxlo : ∀ p ∈ win, S - 1 ≤ xp p) (hxU : ∀ p ∈ win, xp p ≤ U)
    (hmass : ∀ v : ℝ, S - 1 ≤ v →
        (∑ p ∈ win, m p * (if xp p ≤ v then (1 : ℝ) else 0)) ≤ ((1 + ε) * (v + 1) / S - 1) * W) :
    (∑ p ∈ win, m p * hBJS (xp p))
      ≤ ε * W * hBJS (S - 1) + (1 + ε) * ((1 / S) * (∫ u in (S - 1)..U, hBJS u)) * W := by
  -- Step 1: termwise FTC decomposition
  have hdecomp : (∑ p ∈ win, m p * hBJS (xp p))
      = (∑ p ∈ win, m p) * hBJS U + ∑ p ∈ win, m p * (∫ v in (xp p)..U, Kh v) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hBJS_ftc (xp p) U (hxU p hp)]; ring
  -- Step 2: swap the sum of integrals into the profile integral
  have hswap : (∑ p ∈ win, m p * (∫ v in (xp p)..U, Kh v))
      = ∫ v in (S - 1)..U, ∑ p ∈ win, (m p * (if xp p ≤ v then Kh v else 0)) := by
    rw [intervalIntegral.integral_finsetSum (fun p _ =>
        (Kh_indicator_intervalIntegrable (xp p) (S - 1) U).const_mul (m p))]
    apply Finset.sum_congr rfl
    intro p hp
    rw [intervalIntegral.integral_const_mul,
        prime_indicator_integral (xp p) (S - 1) U (hxlo p hp) (hxU p hp)]
  -- integrability of the profile
  have hLHS_ii : IntervalIntegrable
      (fun v => ∑ p ∈ win, m p * (if xp p ≤ v then Kh v else 0)) volume (S - 1) U := by
    have hfun : (fun v => ∑ p ∈ win, m p * (if xp p ≤ v then Kh v else 0))
        = ∑ p ∈ win, (fun v => m p * (if xp p ≤ v then Kh v else 0)) := by
      funext v; simp only [Finset.sum_apply]
    rw [hfun]
    exact IntervalIntegrable.sum win (fun p _ =>
      (Kh_indicator_intervalIntegrable (xp p) (S - 1) U).const_mul (m p))
  have hBcont : Continuous (fun v : ℝ => (1 + ε) * (v + 1) / S - 1) := by fun_prop
  have hRHS_ii : IntervalIntegrable
      (fun v => ((1 + ε) * (v + 1) / S - 1) * W * Kh v) volume (S - 1) U :=
    (Kh_intervalIntegrable (S - 1) U).continuousOn_mul (hBcont.mul continuous_const).continuousOn
  -- Step 2': profile ≤ affine-mass integrand pointwise
  have hprofile_le : (∫ v in (S - 1)..U, ∑ p ∈ win, (m p * (if xp p ≤ v then Kh v else 0)))
      ≤ ∫ v in (S - 1)..U, ((1 + ε) * (v + 1) / S - 1) * W * Kh v := by
    apply intervalIntegral.integral_mono_on (by linarith) hLHS_ii hRHS_ii
    intro v hv
    have heq : (∑ p ∈ win, m p * (if xp p ≤ v then Kh v else 0))
        = (∑ p ∈ win, m p * (if xp p ≤ v then (1 : ℝ) else 0)) * Kh v := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _; split_ifs with h <;> ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hmass v hv.1) (Kh_nonneg v)
  -- Step 3: total mass at U
  have hMU : (∑ p ∈ win, m p) ≤ ((1 + ε) * (U + 1) / S - 1) * W := by
    have hh := hmass U hSU
    have heqU : (∑ p ∈ win, m p * (if xp p ≤ U then (1 : ℝ) else 0)) = ∑ p ∈ win, m p := by
      apply Finset.sum_congr rfl
      intro p hp; rw [if_pos (hxU p hp), mul_one]
    rwa [heqU] at hh
  -- Step 4: integration by parts
  have hBderiv : ∀ x, HasDerivAt (fun v => (1 + ε) * (v + 1) / S - 1) ((1 + ε) / S) x := by
    intro x
    have h0 := (((hasDerivAt_id x).add_const (1 : ℝ)).const_mul (1 + ε)).div_const S
    simpa using h0.sub_const 1
  have hBS1 : (1 + ε) * ((S - 1) + 1) / S - 1 = ε := by
    rw [show (S - 1) + 1 = S by ring, mul_div_assoc, div_self hS.ne', mul_one]; ring
  have hmaster := hBJS_ibp_master (fun v => (1 + ε) * (v + 1) / S - 1) (fun _ => (1 + ε) / S)
    hBderiv continuous_const (S - 1) U (by linarith)
  rw [hBS1] at hmaster
  have hf_ii : IntervalIntegrable (fun v => (1 + ε) / S * hBJS v) volume (S - 1) U :=
    (hBJS_intervalIntegrable (S - 1) U).const_mul _
  have hg_ii : IntervalIntegrable (fun v => ((1 + ε) * (v + 1) / S - 1) * Kh v) volume (S - 1) U :=
    (Kh_intervalIntegrable (S - 1) U).continuousOn_mul hBcont.continuousOn
  rw [intervalIntegral.integral_sub hf_ii hg_ii, intervalIntegral.integral_const_mul] at hmaster
  -- hmaster now: (1+ε)/S * ∫hBJS - ∫ B·Kh = B U · hBJS U - ε · hBJS(S-1)
  have hIBP : (∫ v in (S - 1)..U, ((1 + ε) * (v + 1) / S - 1) * Kh v)
      = (1 + ε) / S * (∫ v in (S - 1)..U, hBJS v)
        - ((1 + ε) * (U + 1) / S - 1) * hBJS U + ε * hBJS (S - 1) := by
    linarith [hmaster]
  have hWconst : (∫ v in (S - 1)..U, ((1 + ε) * (v + 1) / S - 1) * W * Kh v)
      = W * ∫ v in (S - 1)..U, ((1 + ε) * (v + 1) / S - 1) * Kh v := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _; ring
  -- Combine
  calc (∑ p ∈ win, m p * hBJS (xp p))
      = (∑ p ∈ win, m p) * hBJS U + ∑ p ∈ win, m p * (∫ v in (xp p)..U, Kh v) := hdecomp
    _ ≤ ((1 + ε) * (U + 1) / S - 1) * W * hBJS U
          + ∫ v in (S - 1)..U, ((1 + ε) * (v + 1) / S - 1) * W * Kh v := by
        rw [hswap]
        exact add_le_add (mul_le_mul_of_nonneg_right hMU (hBJS_pos U).le) hprofile_le
    _ = ((1 + ε) * (U + 1) / S - 1) * W * hBJS U
          + W * ∫ v in (S - 1)..U, ((1 + ε) * (v + 1) / S - 1) * Kh v := by rw [hWconst]
    _ = ε * W * hBJS (S - 1) + (1 + ε) * ((1 / S) * (∫ u in (S - 1)..U, hBJS u)) * W := by
        rw [hIBP]; ring

/-! ## Part 5 — `hpush`: the IBP core for the `S ≥ 2` cells -/

/-- **The pushforward core `hpush`** (Floor A).  The discrete → integral reconstruction that the
landed `hh_sharp_ge2_of_pushforward` consumes: for a window `win` of prime factors with the sieve
guards of `upset_mass_le`, the descending-`V` `hBJS`-sum is bounded by the `z`-edge boundary defect
plus the `(1+ε)(1/S)∫` main term.  Instantiates `layer_cake_pushforward` with the mass control
`upset_mass_le`. -/
theorem hpush_core (s' : BoundingSieve) (ε : ℝ) (z D' : ℕ)
    (hε : 0 ≤ ε)
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (hS1 : 1 ≤ logRatio z D')
    (win : Finset ℕ) (hsub : win ⊆ s'.prodPrimes.primeFactors)
    (U : ℝ) (hU : ∀ p ∈ win, logRatio p D' - 1 ≤ U) (hUS : logRatio z D' - 1 ≤ U) :
    ∑ p ∈ win, s'.nu p * Vbelow s' p * hBJS (logRatio p D' - 1)
      ≤ ε * Salt.BrunLower.W s' * hBJS (logRatio z D' - 1)
        + (1 + ε) * ((1 / logRatio z D') * (∫ u in (logRatio z D' - 1)..U, hBJS u))
            * Salt.BrunLower.W s' := by
  have hWpos : 0 < Salt.BrunLower.W s' := Salt.BrunLower.W_pos s'
  have hS0 : 0 < logRatio z D' := by linarith [hS1]
  -- log positivity (for the point lower bound)
  have hlz_nn : (0 : ℝ) ≤ Real.log z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlogz : 0 < Real.log z := by
    rcases lt_or_eq_of_le hlz_nn with h | h
    · exact h
    · exfalso; rw [logRatio, ← h, div_zero] at hS1; linarith
  have hzD : Real.log z ≤ Real.log D' := by
    have h := hS1; rw [logRatio, le_div_iff₀ hlogz, one_mul] at h; exact h
  have hlogD : 0 < Real.log D' := lt_of_lt_of_le hlogz hzD
  -- masses nonneg
  have hm_nonneg : ∀ p ∈ win, 0 ≤ s'.nu p * Vbelow s' p := by
    intro p hp
    have hppf := hsub hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hppf
    have hdvd : p ∣ s'.prodPrimes := Nat.dvd_of_mem_primeFactors hppf
    exact mul_nonneg (s'.nu_pos_of_prime p hpp hdvd).le (Vbelow_pos s' p).le
  -- points ≥ S-1
  have hxlo : ∀ p ∈ win, logRatio z D' - 1 ≤ logRatio p D' - 1 := by
    intro p hp
    have hppf := hsub hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hppf
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    have hpz : (p : ℝ) < (z : ℝ) := by exact_mod_cast hz p hppf
    have hlpz : Real.log p ≤ Real.log z := Real.log_le_log (by linarith) hpz.le
    have : logRatio z D' ≤ logRatio p D' := by
      rw [logRatio, logRatio]; exact div_le_div_of_nonneg_left hlogD.le hlogp hlpz
    linarith
  -- apply the generic engine
  apply layer_cake_pushforward (fun p => s'.nu p * Vbelow s' p) (fun p => logRatio p D' - 1)
    win (Salt.BrunLower.W s') (logRatio z D') U ε hWpos hS0 hUS hm_nonneg hxlo hU
  -- the affine mass control from `upset_mass_le`
  intro v hv
  have hmass := upset_mass_le s' ε z D' (v + 1) hε hz hguard hnu hS1 (by linarith)
  calc (∑ p ∈ win, s'.nu p * Vbelow s' p * (if (logRatio p D' - 1 : ℝ) ≤ v then (1 : ℝ) else 0))
      = ∑ p ∈ win.filter (fun p => (logRatio p D' - 1 : ℝ) ≤ v), s'.nu p * Vbelow s' p := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p _; split_ifs with h <;> simp
    _ ≤ ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => (logRatio p D' : ℝ) ≤ v + 1),
          s'.nu p * Vbelow s' p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_filter] at hp ⊢
          exact ⟨hsub hp.1, by linarith [hp.2]⟩
        · intro p hp _
          have hppf := (Finset.mem_filter.mp hp).1
          have hpp : p.Prime := Nat.prime_of_mem_primeFactors hppf
          have hdvd : p ∣ s'.prodPrimes := Nat.dvd_of_mem_primeFactors hppf
          exact mul_nonneg (s'.nu_pos_of_prime p hpp hdvd).le (Vbelow_pos s' p).le
    _ ≤ ((1 + ε) * (v + 1) / logRatio z D' - 1) * Salt.BrunLower.W s' := hmass

/-! ## Part 6 — the window-relative mass control (the flat cell's catch-#34 fix) -/

/-- **The window-relative up-set mass bound** (catch #34's fix).  For the side'=1 window
`win = {p : p³ < D'}`, the descending-`V` mass of the primes with `logRatio p D' ≤ t` obeys
`Σ ≤ ((1+ε)·t/3 − 1)·Vlow` — anchored at the window's own threshold `D'^{1/3}` (so `S_window = 3`)
against `Vlow = V(D'^{1/3})`, not the full `W`.  This is the `upset_mass_le` argument with
`z := D'^{1/3}` (`log z = log D'/3`) and `W := Vlow`; the tighter anchor removes the spurious
`v = 2` boundary defect that made the full-`pf` bound too loose on the flat cell. -/
theorem upset_mass_window_le (s' : BoundingSieve) (ε : ℝ) (D' : ℕ) (t : ℝ)
    (hε : 0 ≤ ε) (hlogD : 0 < Real.log D')
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (ht3 : 3 ≤ t) :
    ∑ p ∈ (s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D')).filter
          (fun p => (logRatio p D' : ℝ) ≤ t),
        s'.nu p * Vbelow s' p
      ≤ ((1 + ε) * t / 3 - 1) * Vlow s' D' := by
  classical
  have hVlow := Vlow_pos s' D'
  have htpos : (0 : ℝ) < t := by linarith
  have hDpos : (0 : ℝ) < (D' : ℝ) := by
    rcases Nat.eq_zero_or_pos D' with h | h
    · rw [h] at hlogD; simp at hlogD
    · exact_mod_cast h
  -- the window's own threshold `zw = D'^{1/3}` and the up-set threshold `tN = ⌈D'^{1/t}⌉`
  set zw := Real.exp (Real.log D' / 3) with hzwdef
  have hzw_pos : 0 < zw := Real.exp_pos _
  set wexp := Real.exp (Real.log D' / t) with hwexp
  set tN := ⌈wexp⌉₊ with htN
  set win := s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D') with hwindef
  -- the up-set filter coincides with `tN ≤ p` on the window
  have hfilter : win.filter (fun p => (logRatio p D' : ℝ) ≤ t) = win.filter (fun p => tN ≤ p) := by
    apply Finset.filter_congr
    intro p hp
    have hppf : p ∈ s'.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hppf
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    constructor
    · intro hle
      rw [logRatio, div_le_iff₀ hlogp] at hle
      have hdle : Real.log D' / t ≤ Real.log p := by rw [div_le_iff₀ htpos]; linarith
      exact Nat.ceil_le.mpr (by rw [hwexp]; exact (Real.le_log_iff_exp_le hp0).mp hdle)
    · intro hle
      have hwle : wexp ≤ (p : ℝ) := le_trans (Nat.le_ceil wexp) (by exact_mod_cast hle)
      rw [hwexp] at hwle
      have hdle : Real.log D' / t ≤ Real.log p := (Real.le_log_iff_exp_le hp0).mpr hwle
      rw [logRatio, div_le_iff₀ hlogp]; rw [div_le_iff₀ htpos] at hdle; linarith
  rw [hfilter]
  set F := win.filter (fun p => tN ≤ p) with hFdef
  -- membership facts: window primes are `< zw`
  have hp_lt_zw : ∀ p ∈ win, (p : ℝ) < zw := by
    intro p hp
    have hppf : p ∈ s'.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
    have hp3 : p ^ 3 < D' := (Finset.mem_filter.mp hp).2
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hppf
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp3 : 3 * Real.log p < Real.log D' := by
      have hpr : ((p : ℝ)) ^ 3 < (D' : ℝ) := by exact_mod_cast hp3
      have h1 := Real.log_lt_log (show (0:ℝ) < (p:ℝ)^3 by positivity) hpr
      rw [Real.log_pow] at h1; push_cast at h1; linarith
    rw [hzwdef]
    have hlt : Real.log p < Real.log D' / 3 := by rw [lt_div_iff₀ (by norm_num)]; linarith
    calc (p : ℝ) = Real.exp (Real.log p) := (Real.exp_log hp0).symm
      _ < Real.exp (Real.log D' / 3) := Real.exp_lt_exp.mpr hlt
  -- the window-relative telescope: `Σ_F ν·Vbelow = Vbelow(tN) − Vlow`
  have hincr : ∀ p ∈ win, (∏ q ∈ win.filter (· < p), (1 - s'.nu q)) = Vbelow s' p := by
    intro p hp
    have hp3 : p ^ 3 < D' := (Finset.mem_filter.mp hp).2
    rw [Vbelow, belowPrimes]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext q
    simp only [Finset.mem_filter, hwindef]
    constructor
    · rintro ⟨⟨hqpf, _⟩, hqp⟩; exact ⟨hqpf, hqp⟩
    · rintro ⟨hqpf, hqp⟩
      refine ⟨⟨hqpf, ?_⟩, hqp⟩
      have hqp' : q < p := hqp
      calc q ^ 3 < p ^ 3 := by
              apply Nat.pow_lt_pow_left hqp' (by norm_num)
        _ < D' := hp3
  have hlowprod : (∏ q ∈ win.filter (· < tN), (1 - s'.nu q)) = Vbelow s' tN := by
    rw [Vbelow, belowPrimes]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext q
    simp only [Finset.mem_filter, hwindef]
    constructor
    · rintro ⟨⟨hqpf, _⟩, hqt⟩; exact ⟨hqpf, hqt⟩
    · rintro ⟨hqpf, hqt⟩
      refine ⟨⟨hqpf, ?_⟩, hqt⟩
      -- q < tN ≤ wexp+1 ≤ zw, so q³ < D'
      have hqpp : q.Prime := Nat.prime_of_mem_primeFactors hqpf
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqpp.two_le
      have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
      have hqwexp : (q : ℝ) < wexp := Nat.lt_ceil.mp hqt
      have hlogq : Real.log q < Real.log D' / t := by
        rw [hwexp] at hqwexp
        have := Real.log_lt_log hq0 hqwexp
        rwa [Real.log_exp] at this
      have h3lt : 3 * Real.log q < Real.log D' := by
        have hlt3 : Real.log q < Real.log D' / 3 :=
          lt_of_lt_of_le hlogq (div_le_div_of_nonneg_left hlogD.le (by norm_num) ht3)
        linarith
      have hlq3 : Real.log ((q : ℝ) ^ 3) < Real.log D' := by
        rw [Real.log_pow]; push_cast; linarith
      have hcube : ((q : ℝ)) ^ 3 < (D' : ℝ) :=
        (Real.log_lt_log_iff (by positivity) hDpos).mp hlq3
      exact_mod_cast hcube
  have hmass_eq : ∑ p ∈ F, s'.nu p * Vbelow s' p = Vbelow s' tN - Vlow s' D' := by
    have htel := telescope_ge win s'.nu tN
    rw [hFdef]
    calc ∑ p ∈ win.filter (fun p => tN ≤ p), s'.nu p * Vbelow s' p
        = ∑ p ∈ win.filter (tN ≤ ·), s'.nu p * ∏ q ∈ win.filter (· < p), (1 - s'.nu q) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hincr p (Finset.mem_filter.mp hp).1]
      _ = (∏ q ∈ win.filter (· < tN), (1 - s'.nu q)) - ∏ p ∈ win, (1 - s'.nu p) := htel
      _ = Vbelow s' tN - Vlow s' D' := by rw [hlowprod]; simp only [Vlow, hwindef]
  rw [hmass_eq]
  -- the V-ratio bound `Vbelow(tN) ≤ (1+ε)·t/3·Vlow`
  have hFprod_pos : 0 < ∏ p ∈ F, (1 - s'.nu p) := by
    apply Finset.prod_pos
    intro p hp
    have hpwin : p ∈ win := (Finset.mem_filter.mp hp).1
    have hppf : p ∈ s'.prodPrimes.primeFactors := (Finset.mem_filter.mp hpwin).1
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hppf
    have hdvd : p ∣ s'.prodPrimes := Nat.dvd_of_mem_primeFactors hppf
    have := s'.nu_lt_one_of_prime p hpp hdvd; linarith
  -- `Vlow = Vbelow(tN) · ∏_F`
  have hVlowsplit : Vlow s' D' = Vbelow s' tN * ∏ p ∈ F, (1 - s'.nu p) := by
    have hvl : Vlow s' D' = ∏ p ∈ win, (1 - s'.nu p) := by simp only [Vlow, hwindef]
    rw [hvl, ← hlowprod, ← Finset.prod_filter_mul_prod_filter_not win (· < tN)]
    congr 1
    rw [hFdef]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr; intro p _; simp only [not_lt]
  have hVratio : (∏ p ∈ F, (1 - s'.nu p))⁻¹ ≤ (1 + ε) * t / 3 := by
    rcases F.eq_empty_or_nonempty with hFe | hFne
    · rw [hFe, Finset.prod_empty, inv_one]
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3)]; nlinarith [ht3, hε]
    · set p₀ := F.min' hFne with hp₀
      have hp₀F : p₀ ∈ F := F.min'_mem hFne
      have hp₀win : p₀ ∈ win := (Finset.mem_filter.mp hp₀F).1
      have hp₀pf : p₀ ∈ s'.prodPrimes.primeFactors := (Finset.mem_filter.mp hp₀win).1
      obtain ⟨hp₀3, hp₀thr⟩ := hguard p₀ hp₀pf
      have hp₀zw : (p₀ : ℝ) ≤ zw := le_of_lt (hp_lt_zw p₀ hp₀win)
      have hmain := vratio_prod_le s' F hε hp₀3 hp₀zw hp₀thr (fun p hp => by
        have hpwin : p ∈ win := (Finset.mem_filter.mp hp).1
        have hppf : p ∈ s'.prodPrimes.primeFactors := (Finset.mem_filter.mp hpwin).1
        exact ⟨Nat.prime_of_mem_primeFactors hppf, by exact_mod_cast F.min'_le p hp,
          hp_lt_zw p hpwin, hnu p hppf⟩)
      -- `(1+ε)·log zw/log p₀ = (1+ε)/3·logRatio p₀ D' ≤ (1+ε)t/3`
      have hp₀pp : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀pf
      have hp₀2 : (2 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀pp.two_le
      have hlogp₀ : 0 < Real.log p₀ := Real.log_pos (by linarith)
      have hp₀t : (logRatio p₀ D' : ℝ) ≤ t := by
        have hmem : p₀ ∈ win.filter (fun p => (logRatio p D' : ℝ) ≤ t) := by
          rw [hfilter]; exact hp₀F
        exact (Finset.mem_filter.mp hmem).2
      have hp₀t' : Real.log D' ≤ t * Real.log p₀ := by
        rw [logRatio, div_le_iff₀ hlogp₀] at hp₀t; exact hp₀t
      have hlogzw : Real.log zw = Real.log D' / 3 := by rw [hzwdef, Real.log_exp]
      have hzwp : Real.log zw / Real.log p₀ ≤ t / 3 := by
        rw [hlogzw, div_le_div_iff₀ hlogp₀ (by norm_num : (0:ℝ) < 3)]
        nlinarith [hp₀t', hlogp₀]
      calc (∏ p ∈ F, (1 - s'.nu p))⁻¹ ≤ (1 + ε) * Real.log zw / Real.log p₀ := hmain
        _ = (1 + ε) * (Real.log zw / Real.log p₀) := by ring
        _ ≤ (1 + ε) * (t / 3) := mul_le_mul_of_nonneg_left hzwp (by linarith)
        _ = (1 + ε) * t / 3 := by ring
  have hVeq : Vbelow s' tN = Vlow s' D' * (∏ p ∈ F, (1 - s'.nu p))⁻¹ := by
    rw [hVlowsplit, mul_assoc, mul_inv_cancel₀ (ne_of_gt hFprod_pos), mul_one]
  have hVbtN : Vbelow s' tN ≤ (1 + ε) * t / 3 * Vlow s' D' := by
    rw [hVeq]
    calc Vlow s' D' * (∏ p ∈ F, (1 - s'.nu p))⁻¹
        ≤ Vlow s' D' * ((1 + ε) * t / 3) := mul_le_mul_of_nonneg_left hVratio hVlow.le
      _ = (1 + ε) * t / 3 * Vlow s' D' := by ring
  calc Vbelow s' tN - Vlow s' D'
      ≤ (1 + ε) * t / 3 * Vlow s' D' - Vlow s' D' := by linarith [hVbtN]
    _ = ((1 + ε) * t / 3 - 1) * Vlow s' D' := by ring

/-- `hBJS 2 ≤ 4·hBJS S` for `1 ≤ S ≤ 3` (the flat-cell boundary shift, fixed point `2`). -/
theorem hBJS_two_le {S : ℝ} (_hS1 : 1 ≤ S) (hS3 : S ≤ 3) : hBJS 2 ≤ 4 * hBJS S := by
  rw [hBJS_le2 (le_refl 2)]
  rcases le_total S 2 with h | h
  · rw [hBJS_le2 h]; nlinarith [Real.exp_pos (-2 : ℝ)]
  · rw [hBJS_mid h hS3]
    have hid : Real.exp (-2) = Real.exp (S - 2) * Real.exp (-S) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hid]
    have hle : Real.exp (S - 2) ≤ 4 := by
      calc Real.exp (S - 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
        _ ≤ 4 := by have := Real.exp_one_lt_d9; linarith
    nlinarith [hle, Real.exp_pos (-S)]

/-! ## Part 7 — the flat cell (side' = 1, `S ∈ [1,3)`) via the window-relative pushforward -/

/-- **The flat-cell closure** (side' = 1, `S ∈ [1,3)`).  Reuses `layer_cake_pushforward` at
`S := 3`, `W := Vlow` with the window-relative mass control `upset_mass_window_le` (whose fixed
`S = 3` produces the fixed lower limit `2`), then closes with `flat_h_contract` (`97/100`) and the
`h4`-shape `Vlow ≤ (3(1+ε)/S)·W` — the `3` cancels the `1/3`, giving `(1+ε)²(97/100) + O(ε)`.  The
`ε ≤ 1/1000` window is comfortable at the frozen `ε_sieve = 2·10⁻⁸`. -/
theorem hh_sharp_flat (s' : BoundingSieve) (ε : ℝ) (z D' : ℕ)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000) (hD : 1 ≤ D')
    (hS1 : 1 ≤ logRatio z D') (hS3 : logRatio z D' ≤ 3)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (h4 : Vlow s' D' ≤ (3 * (1 + ε) / logRatio z D') * Salt.BrunLower.W s') :
    ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D'),
        s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p))
      ≤ Salt.BrunLower.W s' * (chSharpB ε * hBJS (logRatio z D')) := by
  have hWpos : 0 < Salt.BrunLower.W s' := Salt.BrunLower.W_pos s'
  have hVlowpos : 0 < Vlow s' D' := Vlow_pos s' D'
  have hSpos : (0 : ℝ) < logRatio z D' := by linarith
  have hSpos_bJS : 0 < hBJS (logRatio z D') := hBJS_pos _
  -- log positivity
  have hlz_nn : (0 : ℝ) ≤ Real.log z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlogz : 0 < Real.log z := by
    rcases lt_or_eq_of_le hlz_nn with h | h
    · exact h
    · exfalso; rw [logRatio, ← h, div_zero] at hS1; linarith
  have hzD : Real.log z ≤ Real.log D' := by
    have h := hS1; rw [logRatio, le_div_iff₀ hlogz, one_mul] at h; exact h
  have hlogD : 0 < Real.log D' := lt_of_lt_of_le hlogz hzD
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set win := s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D') with hwindef
  set U := Real.log D' / Real.log 2 + 2 with hUdef
  have hwin_prime : ∀ p ∈ win, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hm_nonneg : ∀ p ∈ win, 0 ≤ s'.nu p * Vbelow s' p := by
    intro p hp
    have hppf := (Finset.mem_filter.mp hp).1
    exact mul_nonneg (s'.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hppf)
      (Nat.dvd_of_mem_primeFactors hppf)).le (Vbelow_pos s' p).le
  have hxlo : ∀ p ∈ win, (3 : ℝ) - 1 ≤ logRatio p D' - 1 := by
    intro p hp
    have hp3 : p ^ 3 < D' := (Finset.mem_filter.mp hp).2
    have hpp : p.Prime := hwin_prime p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    have h3lp : 3 * Real.log p < Real.log D' := by
      have hpr : ((p : ℝ)) ^ 3 < (D' : ℝ) := by exact_mod_cast hp3
      have h1 := Real.log_lt_log (show (0:ℝ) < (p:ℝ)^3 by positivity) hpr
      rw [Real.log_pow] at h1; push_cast at h1; linarith
    have : (3 : ℝ) ≤ logRatio p D' := by rw [logRatio, le_div_iff₀ hlogp]; linarith
    linarith
  have hxU : ∀ p ∈ win, logRatio p D' - 1 ≤ U := by
    intro p hp
    have hpp : p.Prime := hwin_prime p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    have hlog2p : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    have hle : logRatio p D' ≤ Real.log D' / Real.log 2 := by
      rw [logRatio]; exact div_le_div_of_nonneg_left hlogD.le hlog2 hlog2p
    simp only [hUdef]; linarith
  have hSU : (3 : ℝ) - 1 ≤ U := by
    simp only [hUdef]; have : (0:ℝ) ≤ Real.log D' / Real.log 2 := div_nonneg hlogD.le hlog2.le
    linarith
  -- the window-relative layer cake at S := 3, W := Vlow
  have hlc := layer_cake_pushforward (fun p => s'.nu p * Vbelow s' p) (fun p => logRatio p D' - 1)
    win (Vlow s' D') 3 U ε hVlowpos (by norm_num) hSU hm_nonneg hxlo hxU (by
      intro v hv
      have hcalc : (∑ p ∈ win, s'.nu p * Vbelow s' p
            * (if (logRatio p D' - 1 : ℝ) ≤ v then (1:ℝ) else 0))
          = ∑ p ∈ win.filter (fun p => (logRatio p D' : ℝ) ≤ v + 1), s'.nu p * Vbelow s' p := by
        conv_rhs => rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        by_cases h : (logRatio p D' : ℝ) ≤ v + 1
        · rw [if_pos h, if_pos (show (logRatio p D' - 1 : ℝ) ≤ v by linarith), mul_one]
        · rw [if_neg h, if_neg (show ¬ (logRatio p D' - 1 : ℝ) ≤ v by linarith), mul_zero]
      rw [hcalc, hwindef]
      exact upset_mass_window_le s' ε D' (v + 1) hε hlogD hguard hnu (by linarith))
  rw [show (3 : ℝ) - 1 = 2 from by norm_num] at hlc
  -- antitone majorization: cdiv-form ≤ (logRatio − 1)-form
  have hanti := hh_antitone_majorize s' D' hD win hwin_prime hm_nonneg
  -- the numeric close
  set A := ∫ u in (2 : ℝ)..U, hBJS u with hAdef
  have hA_nn : 0 ≤ A :=
    intervalIntegral.integral_nonneg (by linarith [hSU]) (fun u _ => (hBJS_pos u).le)
  have hfc := flat_h_contract (logRatio z D') U hS1 hS3
  have hBJS2 := hBJS_two_le hS1 hS3
  -- main term: (1+ε)·(1/3)·A·Vlow ≤ (1+ε)²·(97/100)·hBJS S·W
  have hAle : A ≤ (logRatio z D') * ((97 / 100) * hBJS (logRatio z D')) := by
    have h := mul_le_mul_of_nonneg_left hfc hSpos.le
    rwa [← mul_assoc, mul_one_div, div_self hSpos.ne', one_mul] at h
  have hmain : (1 + ε) * ((1 / 3) * A) * Vlow s' D'
      ≤ (1 + ε) ^ 2 * (97 / 100) * hBJS (logRatio z D') * Salt.BrunLower.W s' := by
    have hAVl : A * Vlow s' D'
        ≤ ((logRatio z D') * ((97 / 100) * hBJS (logRatio z D'))) *
            ((3 * (1 + ε) / logRatio z D') * Salt.BrunLower.W s') :=
      mul_le_mul hAle h4 hVlowpos.le
        (mul_nonneg hSpos.le (mul_nonneg (by norm_num) hSpos_bJS.le))
    have hcoef : (0 : ℝ) ≤ (1 + ε) * (1 / 3) :=
      mul_nonneg (by linarith) (by norm_num)
    calc (1 + ε) * ((1 / 3) * A) * Vlow s' D'
        = (1 + ε) * (1 / 3) * (A * Vlow s' D') := by ring
      _ ≤ (1 + ε) * (1 / 3) *
            (((logRatio z D') * ((97 / 100) * hBJS (logRatio z D'))) *
              ((3 * (1 + ε) / logRatio z D') * Salt.BrunLower.W s')) :=
            mul_le_mul_of_nonneg_left hAVl hcoef
      _ = (1 + ε) ^ 2 * (97 / 100) * hBJS (logRatio z D') * Salt.BrunLower.W s' := by
            field_simp [hSpos.ne']
  -- boundary term: ε·Vlow·hBJS 2 ≤ 12·ε·(1+ε)·hBJS S·W
  have hbdry : ε * Vlow s' D' * hBJS 2
      ≤ 12 * ε * (1 + ε) * hBJS (logRatio z D') * Salt.BrunLower.W s' := by
    have hSinv : (1 : ℝ) / logRatio z D' ≤ 1 := by
      rw [div_le_one hSpos]; exact hS1
    have hVh : Vlow s' D' * hBJS 2
        ≤ ((3 * (1 + ε) / logRatio z D') * Salt.BrunLower.W s') * (4 * hBJS (logRatio z D')) :=
      mul_le_mul h4 hBJS2 (hBJS_pos 2).le (le_trans hVlowpos.le h4)
    have hRnn : (0 : ℝ) ≤ 12 * ε * (1 + ε) * hBJS (logRatio z D') * Salt.BrunLower.W s' :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε)
        (by linarith)) hSpos_bJS.le) hWpos.le
    calc ε * Vlow s' D' * hBJS 2 = ε * (Vlow s' D' * hBJS 2) := by ring
      _ ≤ ε * (((3 * (1 + ε) / logRatio z D') * Salt.BrunLower.W s')
              * (4 * hBJS (logRatio z D'))) :=
            mul_le_mul_of_nonneg_left hVh hε
      _ = (12 * ε * (1 + ε) * hBJS (logRatio z D') * Salt.BrunLower.W s')
              * (1 / logRatio z D') := by
            ring
      _ ≤ 12 * ε * (1 + ε) * hBJS (logRatio z D') * Salt.BrunLower.W s' :=
            mul_le_of_le_one_right hRnn hSinv
  have hnum : (1 + ε) ^ 2 * (97 / 100) + 12 * ε * (1 + ε) ≤ chSharpB ε := by
    unfold chSharpB; nlinarith [hε, hεsmall, sq_nonneg ε]
  calc ∑ p ∈ win, s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p))
      ≤ ∑ p ∈ win, s'.nu p * Vbelow s' p * hBJS (logRatio p D' - 1) := hanti
    _ ≤ ε * Vlow s' D' * hBJS 2 + (1 + ε) * ((1 / 3) * A) * Vlow s' D' := hlc
    _ ≤ 12 * ε * (1 + ε) * hBJS (logRatio z D') * Salt.BrunLower.W s'
          + (1 + ε) ^ 2 * (97 / 100) * hBJS (logRatio z D') * Salt.BrunLower.W s' :=
        add_le_add hbdry hmain
    _ = ((1 + ε) ^ 2 * (97 / 100) + 12 * ε * (1 + ε))
          * (Salt.BrunLower.W s' * hBJS (logRatio z D')) := by ring
    _ ≤ chSharpB ε * (Salt.BrunLower.W s' * hBJS (logRatio z D')) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = Salt.BrunLower.W s' * (chSharpB ε * hBJS (logRatio z D')) := by ring

/-! ## Part 8 — the closed `S ≥ 2` cell (`hpush_core` ∘ landed scaffold) -/

/-- **The `S ≥ 2` cell closure** (side' = 2 and side' = 1 with `S ≥ 3`).  Composes the IBP core
`hpush_core` with the landed `hh_sharp_ge2_of_pushforward`, choosing the window top
`U = log D'/log 2` (which dominates every `logRatio p D'` since `p ≥ 2`).  This is the sharp
`h`-comparison at `chSharpB` on the moving-lower-limit cells. -/
theorem hh_sharp_ge2 (s' : BoundingSieve) (ε : ℝ) (z D' : ℕ)
    (hε : 0 ≤ ε) (hD : 1 ≤ D') (hS2 : 2 ≤ logRatio z D')
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (win : Finset ℕ) (hsub : win ⊆ s'.prodPrimes.primeFactors) :
    ∑ p ∈ win, s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p))
      ≤ Salt.BrunLower.W s' * (chSharpB ε * hBJS (logRatio z D')) := by
  have hS1 : 1 ≤ logRatio z D' := by linarith
  -- log positivity
  have hlz_nn : (0 : ℝ) ≤ Real.log z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlogz : 0 < Real.log z := by
    rcases lt_or_eq_of_le hlz_nn with h | h
    · exact h
    · exfalso; rw [logRatio, ← h, div_zero] at hS1; linarith
  have hzD : Real.log z ≤ Real.log D' := by
    have h := hS1; rw [logRatio, le_div_iff₀ hlogz, one_mul] at h; exact h
  have hlogD : 0 < Real.log D' := lt_of_lt_of_le hlogz hzD
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz2 : Real.log 2 ≤ Real.log z := by
    -- z ≥ 2 since log z > 0
    have hz0 : 0 < z := by
      rcases Nat.eq_zero_or_pos z with h | h
      · rw [h] at hlogz; simp at hlogz
      · exact h
    have hz1 : (1 : ℝ) < z := by
      by_contra hle
      have hle' : (z : ℝ) ≤ 1 := not_lt.mp hle
      have : Real.log z ≤ 0 := Real.log_nonpos (by exact_mod_cast hz0.le) hle'
      linarith
    have h1z : 1 < z := by exact_mod_cast hz1
    have h2z : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 2 ≤ z)
    exact Real.log_le_log (by norm_num) h2z
  set U := Real.log D' / Real.log 2 with hUdef
  have hSU_le : logRatio z D' ≤ U := by
    rw [logRatio, hUdef]; exact div_le_div_of_nonneg_left hlogD.le hlog2 hz2
  have hUS : logRatio z D' - 1 ≤ U := by linarith
  have hU : ∀ p ∈ win, logRatio p D' - 1 ≤ U := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (hsub hp)
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    have hlog2p : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    have : logRatio p D' ≤ U := by
      rw [logRatio, hUdef]; exact div_le_div_of_nonneg_left hlogD.le hlog2 hlog2p
    linarith
  refine hh_sharp_ge2_of_pushforward s' ε z D' hε hD hS2 win
    (fun p hp => Nat.prime_of_mem_primeFactors (hsub hp))
    (fun p hp => mul_nonneg
      (s'.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors (hsub hp))
        (Nat.dvd_of_mem_primeFactors (hsub hp))).le (Vbelow_pos s' p).le) U ?_
  exact hpush_core s' ε z D' hε hz hguard hnu hS1 win hsub U hU hUS

/-! ## Part 9 — the assembled sharp `h`-comparison `hh_sharp_of_window` -/

/-- **The sharp `h`-part windowed comparison** — the `chSharpB` `h`-slot, composed by cases on
`side'` and the operating point `S := logRatio z D'`.  This is the sharp analogue of the crude
`DecayMass.hh_of_window`: same filter `side' % 2 = 1 → p³ < D'`, RHS `W·(chSharpB ε·hBJS S)` in
place of the crude `W·(ch_const n ε·hBJS S)`.  Cases:

* `side' = 2` (`⇒ S ≥ 2` via `loBnd_two`/`hlo`) and `side' = 1, S > 3` — the moving-lower-limit
  cells, closed by `hh_sharp_ge2` (E₁a `49/50` through the `hpush_core` IBP engine);
* `side' = 1, S ∈ [1,3]` — the flat cell, closed by `hh_sharp_flat` (E₁a-flat `97/100`,
  window-relative pushforward), which consumes the threaded Hyp-(4) mass bound `h4` in the
  CONDITIONED form `1 ≤ S → S ≤ 3 → Vlow ≤ (3K/S)·W` (`K ≤ 1+ε`; catch #66/H4C — the
  unconditioned row is false outside the flat cell), applied here at `hS1`/`hle3`.

The `ε ≤ 1/1000` window is comfortable at the frozen `ε_sieve = 2·10⁻⁸`. -/
theorem hh_sharp_of_window (s' : BoundingSieve) (ε K : ℝ) (z side' D' n : ℕ)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε) (_hn : 1 ≤ n) (hD : 1 ≤ D')
    (hside : side' = 1 ∨ side' = 2)
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (hS1 : 1 ≤ logRatio z D')
    (hlo : loBnd side' ≤ logRatio z D')
    (h4 : 1 ≤ logRatio z D' → logRatio z D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s') :
    (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
        s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p)))
      ≤ Salt.BrunLower.W s' * (chSharpB ε * hBJS (logRatio z D')) := by
  have hSpos : (0 : ℝ) < logRatio z D' := by linarith
  rcases hside with rfl | rfl
  · -- side' = 1
    by_cases hle3 : logRatio z D' ≤ 3
    · -- flat cell, S ∈ [1,3]
      have h4' : Vlow s' D' ≤ (3 * (1 + ε) / logRatio z D') * Salt.BrunLower.W s' :=
        le_trans (h4 hS1 hle3) (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by linarith) hSpos.le) (Salt.BrunLower.W_pos s').le)
      have hfilter :
          s'.prodPrimes.primeFactors.filter (fun p => 1 % 2 = 1 → p ^ 3 < D')
            = s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D') :=
        Finset.filter_congr (fun p _ => ⟨fun h => h (by norm_num), fun h _ => h⟩)
      rw [hfilter]
      exact hh_sharp_flat s' ε z D' hε hεsmall hD hS1 hle3 hguard hnu h4'
    · -- S > 3 ⟹ S ≥ 2
      have hS2 : 2 ≤ logRatio z D' := by have := not_le.mp hle3; linarith
      exact hh_sharp_ge2 s' ε z D' hε hD hS2 hz hguard hnu
        (s'.prodPrimes.primeFactors.filter (fun p => 1 % 2 = 1 → p ^ 3 < D'))
        (Finset.filter_subset _ _)
  · -- side' = 2 ⟹ S ≥ 2 (loBnd 2 = 2)
    have hS2 : 2 ≤ logRatio z D' := by rw [loBnd_two] at hlo; exact hlo
    exact hh_sharp_ge2 s' ε z D' hε hD hS2 hz hguard hnu
      (s'.prodPrimes.primeFactors.filter (fun p => 2 % 2 = 1 → p ^ 3 < D'))
      (Finset.filter_subset _ _)

end Salt.Chen
