/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.ZetaPartialFractions
import Mathlib

/-!
# MR-gate wave 1, stone S3 — the all-`t` ζ lower bound assembly (`ZetaLowerAllT`)

Rung card (MR freeze, S3 ZETA-ALLT): the all-`t` lower bound
`c''·(log(|t|+3))^{-3/4}·(loglog(|t|+16))^{-4} ≤ ‖ζ(1+d'+it)‖`, `d' ∈ [0,1]`,
assembled from three ranges:
* `|t| ≥ T₁` — the pow-grade bound (stone S2, `zeta_pow_lower`), consumed here
  through the NAMED HYPOTHESIS slot `hpow` of `zeta_lower_all_t_of_pow`;
* `3 ≤ |t| ≤ T₁` — the **compact-min discharge** (`zeta_lower_compact_mid`):
  `ζ` is continuous and nonvanishing on the box `[1,2] × {3 ≤ |t| ≤ T₁}`
  (`riemannZeta_ne_zero_of_one_le_re` — the classical region has NO height
  threshold), so compactness furnishes a positive minimum.  Nonconstructive
  posture REGISTERED (freeze: "compact-min discharge... eps0 in c3" pattern);
  the design-grade absorbed constant is `≈ loglog T₀ ≈ 1251`.
* `|t| ≤ 3` — the `Zc` pole-patch (`zeta_lower_small_t`), mirroring
  `Zc_patch_lower` (`ZetaInvShallow.lean:104`): `Zc = (s−1)ζ` is continuous and
  nonvanishing on the compact `[1,2] × [−3,3]`, and near the pole the `(s−1)`
  factor only HELPS (`‖ζ‖ = ‖Zc‖/‖s−1‖ ≥ δ/4`).  The single excluded point is
  `s = 1` itself (`d' = 0, t = 0`), where mathlib's `ζ(1)` is a junk value —
  every downstream consumer evaluates at `d' = 1/log x > 0`.

The `+3`/`+16` offsets in the exported denominator make both factors `≥ 1` at
every `t` (`3 > e` and `16 > e^e`), so the constant ranges absorb into `c''`.
Once S2 lands, the closer `zeta_lower_all_t` (end of file) discharges `hpow`.
-/

namespace Salt.MR

open Complex Metric Salt.SW

/-- **S3 mid range — the compact-min discharge (`T₀-FILL`).**  On the box
`Re ∈ [1,2]`, `3 ≤ |Im| ≤ T₁`, the function `ζ` is continuous (no pole: `s ≠ 1`)
and nonvanishing (`Re ≥ 1`), so it attains a positive minimum `ε₀`.
Nonconstructive (extreme-value theorem); `ε₀` may depend on `T₁` arbitrarily. -/
theorem zeta_lower_compact_mid {T₁ : ℝ} (hT₁ : 3 ≤ T₁) :
    ∃ ε₀ > 0, ∀ d' t : ℝ, 0 ≤ d' → d' ≤ 1 → 3 ≤ |t| → |t| ≤ T₁ →
      ε₀ ≤ ‖riemannZeta ((1 + d' : ℝ) + (t : ℝ) * Complex.I)‖ := by
  set B : Set ℂ := {z : ℂ | (1 ≤ z.re ∧ z.re ≤ 2) ∧ (3 ≤ |z.im| ∧ |z.im| ≤ T₁)}
    with hBdef
  have hBeq : B = ({z : ℂ | 1 ≤ z.re} ∩ {z : ℂ | z.re ≤ 2}) ∩
      ({z : ℂ | 3 ≤ |z.im|} ∩ {z : ℂ | |z.im| ≤ T₁}) := by
    ext z
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
  have hBclosed : IsClosed B := by
    rw [hBeq]
    exact ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const)).inter
      ((isClosed_le continuous_const Complex.continuous_im.abs).inter
        (isClosed_le Complex.continuous_im.abs continuous_const))
  have hBsub : B ⊆ closedBall (0 : ℂ) (2 + T₁) := by
    intro z hz
    obtain ⟨⟨h1, h2⟩, _h3, h4⟩ := hz
    rw [mem_closedBall, Complex.dist_eq, sub_zero]
    have hnorm := Complex.norm_le_abs_re_add_abs_im z
    have hre : |z.re| ≤ 2 := by rw [abs_of_pos (by linarith : (0 : ℝ) < z.re)]; exact h2
    linarith
  have hBcompact : IsCompact B :=
    (isCompact_closedBall (0 : ℂ) (2 + T₁)).of_isClosed_subset hBclosed hBsub
  have him23 : ((⟨2, 3⟩ : ℂ)).im = 3 := rfl
  have hBne : B.Nonempty := by
    refine ⟨⟨2, 3⟩, ⟨⟨by norm_num, by norm_num⟩, ?_, ?_⟩⟩
    · rw [him23, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    · rw [him23, abs_of_pos (by norm_num : (0:ℝ) < 3)]; exact hT₁
  have hne_one : ∀ z ∈ B, z ≠ 1 := by
    intro z hz h1
    obtain ⟨_, h3, _⟩ := hz
    rw [h1, Complex.one_im, abs_zero] at h3
    norm_num at h3
  have hcont : ContinuousOn (fun z => ‖riemannZeta z‖) B := by
    intro z hz
    exact ((differentiableAt_riemannZeta (hne_one z hz)).continuousAt.norm).continuousWithinAt
  obtain ⟨z₀, hz₀B, hz₀min⟩ := hBcompact.exists_isMinOn hBne hcont
  have hz₀ne : riemannZeta z₀ ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hz₀B.1.1
  refine ⟨‖riemannZeta z₀‖, norm_pos_iff.mpr hz₀ne, ?_⟩
  intro d' t hd0 hd1 ht3 htT
  set s : ℂ := ((1 + d' : ℝ) : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = 1 + d' := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hmem : s ∈ B := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hsre]; linarith
    · rw [hsre]; linarith
    · rw [hsim]; exact ht3
    · rw [hsim]; exact htT
  exact isMinOn_iff.mp hz₀min s hmem

/-- **S3 small range — the `Zc` pole-patch.**  On `Re ∈ [1,2]`, `|Im| ≤ 3`,
`Zc = (s−1)ζ` is continuous and nonvanishing (the compact-min `δ`), and
`‖s−1‖ ≤ 4`, so `‖ζ(s)‖ ≥ δ/4` away from the excluded point `s = 1`
(`d' = 0 ∧ t = 0`; consumers evaluate at `d' > 0`). -/
theorem zeta_lower_small_t :
    ∃ δ > 0, ∀ d' t : ℝ, 0 ≤ d' → d' ≤ 1 → |t| ≤ 3 → ¬(d' = 0 ∧ t = 0) →
      δ ≤ ‖riemannZeta ((1 + d' : ℝ) + (t : ℝ) * Complex.I)‖ := by
  set P : Set ℂ := {z : ℂ | (1 ≤ z.re ∧ z.re ≤ 2) ∧ |z.im| ≤ 3} with hPdef
  have hPeq : P = ({z : ℂ | 1 ≤ z.re} ∩ {z : ℂ | z.re ≤ 2})
      ∩ {z : ℂ | |z.im| ≤ 3} := by
    ext z
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  have hPclosed : IsClosed P := by
    rw [hPeq]
    exact ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const)).inter
      (isClosed_le Complex.continuous_im.abs continuous_const)
  have hPsub : P ⊆ closedBall (0 : ℂ) 5 := by
    intro z hz
    obtain ⟨⟨h1, h2⟩, h3⟩ := hz
    rw [mem_closedBall, Complex.dist_eq, sub_zero]
    have hnorm := Complex.norm_le_abs_re_add_abs_im z
    have hre : |z.re| ≤ 2 := by rw [abs_of_pos (by linarith : (0 : ℝ) < z.re)]; exact h2
    linarith
  have hPcompact : IsCompact P :=
    (isCompact_closedBall (0 : ℂ) 5).of_isClosed_subset hPclosed hPsub
  have him10 : ((⟨1, 0⟩ : ℂ)).im = 0 := rfl
  have hPne : P.Nonempty := by
    refine ⟨⟨1, 0⟩, ⟨⟨le_refl _, by norm_num⟩, ?_⟩⟩
    rw [him10, abs_zero]; norm_num
  have hZcne : ∀ z ∈ P, Zc z ≠ 0 := by
    intro z hz
    obtain ⟨⟨h1, _h2⟩, _h3⟩ := hz
    rcases eq_or_ne z 1 with rfl | hz1
    · rw [Zc_one]; exact one_ne_zero
    · rw [Zc_eq_of_ne hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (riemannZeta_ne_zero_of_one_le_re h1)
  have hcont : ContinuousOn (fun z => ‖Zc z‖) P :=
    (Zc_differentiable.continuous.norm).continuousOn
  obtain ⟨z₀, hz₀P, hz₀min⟩ := hPcompact.exists_isMinOn hPne hcont
  have hδpos : 0 < ‖Zc z₀‖ := norm_pos_iff.mpr (hZcne z₀ hz₀P)
  refine ⟨‖Zc z₀‖ / 4, by positivity, ?_⟩
  intro d' t hd0 hd1 ht3 hne
  set s : ℂ := ((1 + d' : ℝ) : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = 1 + d' := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hs1 : s ≠ 1 := by
    intro h
    apply hne
    constructor
    · have := congrArg Complex.re h
      rw [hsre, Complex.one_re] at this; linarith
    · have := congrArg Complex.im h
      rw [hsim, Complex.one_im] at this; linarith
  have hmem : s ∈ P := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hsre]; linarith
    · rw [hsre]; linarith
    · rw [hsim]; exact ht3
  have hδs : ‖Zc z₀‖ ≤ ‖Zc s‖ := isMinOn_iff.mp hz₀min s hmem
  have hs1norm : ‖s - 1‖ ≤ 4 := by
    have hre : (s - 1).re = d' := by simp [hsdef]
    have him : (s - 1).im = t := by simp [hsdef]
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    rw [hre, him] at h
    have hab : |d'| ≤ 1 := by rw [abs_of_nonneg hd0]; exact hd1
    linarith
  have hZcs : Zc s = (s - 1) * riemannZeta s := Zc_eq_of_ne hs1
  have h1 : ‖Zc s‖ = ‖s - 1‖ * ‖riemannZeta s‖ := by rw [hZcs, norm_mul]
  have h2 : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 4 * ‖riemannZeta s‖ :=
    mul_le_mul_of_nonneg_right hs1norm (norm_nonneg _)
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  calc ‖Zc z₀‖ ≤ ‖Zc s‖ := hδs
    _ = ‖s - 1‖ * ‖riemannZeta s‖ := h1
    _ ≤ 4 * ‖riemannZeta s‖ := h2
    _ = ‖riemannZeta s‖ * 4 := by ring

/-- **S3 head — the all-`t` assembly, parametric in the pow bound.**  Given the
S2 pow-grade tail bound as the NAMED HYPOTHESIS `hpow` (the freeze's wave-1
`zeta_pow_lower` shape, `|t| ≥ T₁`), the three ranges compose into the uniform
`c''·(log(|t|+3))^{-3/4}·(loglog(|t|+16))^{-4} ≤ ‖ζ(1+d'+it)‖` for ALL `t`
(and all `d' ∈ [0,1]`, excluding only the pole point `d' = 0 ∧ t = 0`).
`c'' = min(c', ε₀, δ)`; the `[3,T₁]` fill constant `ε₀` is the nonconstructive
compact minimum (design-grade value `≈ e^{−1251}`-ish, absorbed). -/
theorem zeta_lower_all_t_of_pow {c' T₁ : ℝ} (hc' : 0 < c') (hT₁ : 3 ≤ T₁)
    (hpow : ∀ d' t : ℝ, 0 ≤ d' → d' ≤ 1 → T₁ ≤ |t| →
      c' / ((Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ))
        ≤ ‖riemannZeta ((1 + d' : ℝ) + (t : ℝ) * Complex.I)‖) :
    ∃ c'' : ℝ, 0 < c'' ∧ ∀ d' t : ℝ, 0 ≤ d' → d' ≤ 1 → ¬(d' = 0 ∧ t = 0) →
      c'' / ((Real.log (|t| + 3)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (|t| + 16))) ^ (4 : ℕ))
        ≤ ‖riemannZeta ((1 + d' : ℝ) + (t : ℝ) * Complex.I)‖ := by
  obtain ⟨ε₀, hε₀, hmid⟩ := zeta_lower_compact_mid hT₁
  obtain ⟨δ, hδ, hsmall⟩ := zeta_lower_small_t
  have hcmin : 0 < min c' (min ε₀ δ) := lt_min hc' (lt_min hε₀ hδ)
  refine ⟨min c' (min ε₀ δ), hcmin, ?_⟩
  intro d' t hd0 hd1 hne
  -- `e < 3` and `e^e < 16` make both denominator factors ≥ 1 at every `t`
  have hexp1 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  have habs0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hlog3_1 : (1 : ℝ) ≤ Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hexp1.le
  have hlogA1 : (1 : ℝ) ≤ Real.log (|t| + 3) :=
    le_trans hlog3_1 (Real.log_le_log (by norm_num) (by linarith))
  have hlog16 : Real.exp 1 ≤ Real.log 16 := by
    have h4log2 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    have h1 := Real.log_two_gt_d9
    have h2 := Real.exp_one_lt_d9
    rw [h4log2]; linarith
  have hloglog16_1 : (1 : ℝ) ≤ Real.log (Real.log 16) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hlog16
  have hlog16pos : (0 : ℝ) < Real.log 16 := lt_of_lt_of_le (Real.exp_pos 1) hlog16
  have hlogB : Real.log 16 ≤ Real.log (|t| + 16) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hloglogB1 : (1 : ℝ) ≤ Real.log (Real.log (|t| + 16)) :=
    le_trans hloglog16_1 (Real.log_le_log hlog16pos hlogB)
  -- the exported denominator is ≥ 1 (and > 0)
  have hfac1 : (1 : ℝ) ≤ (Real.log (|t| + 3)) ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow hlogA1 (by norm_num)
  have hfac2 : (1 : ℝ) ≤ (Real.log (Real.log (|t| + 16))) ^ (4 : ℕ) :=
    one_le_pow₀ hloglogB1
  have hden1 : (1 : ℝ) ≤ (Real.log (|t| + 3)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (|t| + 16))) ^ (4 : ℕ) := by nlinarith [hfac1, hfac2]
  have hdenpos : (0 : ℝ) < (Real.log (|t| + 3)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (|t| + 16))) ^ (4 : ℕ) := by linarith
  rcases le_or_gt |t| 3 with hsm | h3
  · -- SMALL range `|t| ≤ 3` : the `Zc` pole-patch
    exact le_trans (le_trans (div_le_self hcmin.le hden1)
      (le_trans (min_le_right _ _) (min_le_right _ _))) (hsmall d' t hd0 hd1 hsm hne)
  · rcases le_or_gt |t| T₁ with hmd | hT
    · -- MID range `3 ≤ |t| ≤ T₁` : the compact-min fill
      exact le_trans (le_trans (div_le_self hcmin.le hden1)
        (le_trans (min_le_right _ _) (min_le_left _ _))) (hmid d' t hd0 hd1 h3.le hmd)
    · -- TAIL `|t| ≥ T₁` : the pow bound, with denominator monotonicity
      have hb := hpow d' t hd0 hd1 hT.le
      have htgt3 : (3 : ℝ) < |t| := lt_of_le_of_lt hT₁ hT
      have hLpos : (0 : ℝ) < Real.log |t| := Real.log_pos (by linarith)
      have hL1 : (1 : ℝ) < Real.log |t| := by
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) (by linarith)
      have hllpos : (0 : ℝ) < Real.log (Real.log |t|) := Real.log_pos hL1
      have hf1 : (Real.log |t|) ^ ((3 : ℝ) / 4) ≤ (Real.log (|t| + 3)) ^ ((3 : ℝ) / 4) :=
        Real.rpow_le_rpow hLpos.le
          (Real.log_le_log (by linarith) (by linarith)) (by norm_num)
      have hf2 : (Real.log (Real.log |t|)) ^ (4 : ℕ)
          ≤ (Real.log (Real.log (|t| + 16))) ^ (4 : ℕ) :=
        pow_le_pow_left₀ hllpos.le
          (Real.log_le_log hLpos (Real.log_le_log (by linarith) (by linarith))) 4
      have hdenS2pos : (0 : ℝ) < (Real.log |t|) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log |t|)) ^ (4 : ℕ) :=
        mul_pos (Real.rpow_pos_of_pos hLpos _) (pow_pos hllpos 4)
      have hdenle : (Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ)
          ≤ (Real.log (|t| + 3)) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log (|t| + 16))) ^ (4 : ℕ) :=
        mul_le_mul hf1 hf2 (pow_nonneg hllpos.le 4)
          (le_trans (Real.rpow_pos_of_pos hLpos _).le hf1)
      refine le_trans ?_ hb
      rw [div_le_div_iff₀ hdenpos hdenS2pos]
      calc min c' (min ε₀ δ)
            * ((Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ))
          ≤ c' * ((Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ)) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hdenS2pos.le
        _ ≤ c' * ((Real.log (|t| + 3)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (|t| + 16))) ^ (4 : ℕ)) :=
            mul_le_mul_of_nonneg_left hdenle hc'.le

end Salt.MR
