/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.ContourShift
import Salt.MR.PerronSharp

/-!
# S8 MR-CORE, node A3a-R1 — the truncated (discontinuous) Perron kernel

The classical *truncated Perron formula* with explicit error (Montgomery–Vaughan,
*Multiplicative Number Theory I*, Theorem 5.1; Davenport §17): for `c > 0`, `y > 0`,
`y ≠ 1`, `T ≥ 1`,
`(1/2πi) ∫_{c−iT}^{c+iT} yˢ/s ds = 𝟙(y>1) + O(yᶜ/(T·|log y|))`.

mathlib has **no** discontinuous-Perron primitive (its `SW.kernel_identity` uses the
*smoothed* kernel `yˢ/(s(s+1))` to stay absolutely convergent).  We build it from the
residues-lite rectangle apparatus `Salt.SW.ContourShift` — the exact template used by
`Salt.MR.HalaszContour` for the Poisson cosine integral.

## Geometry

The contour integral is the finite vertical segment `Re s = c`, `Im s ∈ [−T, T]`,
parametrised as `I·∫_{−T}^T y^{c+it}/(c+it) dt` (this is `perronContour`).

* **`y > 1`** — close the rectangle `[−R, c] × [−T, T]` to the *left*.  It encloses the
  simple pole of `yˢ/s` at `s = 0` (residue `y⁰ = 1`), so its boundary integral is
  `2πi` (`rectBI_cif_eq` with `φ = yˢ`, `p = 0`).  The two horizontal edges carry the
  error `≤ yᶜ/(T·log y)` each (via `∫ yˣ ≤ yᶜ/log y`); the left edge `Re = −R` is
  `≤ 2T·y^{−R}/R → 0` as `R → ∞`.  Since the segment value is fixed, an
  `ε`-argument (`le_of_forall_pos_le_add`, explicit `R`) discards the left edge.
* **`0 < y < 1`** — close to the *right* `[c, R] × [−T, T]`; no pole, boundary `= 0`
  (`rectBI_eq_zero_of_differentiableOn`); the horizontal edges give the same
  `yᶜ/(T·|log y|)` bound and the right edge `Re = R` vanishes.

## What lands

* `perron_gt_one` — `‖perronContour y c T − 2πi‖ ≤ 2·yᶜ/(T·log y)` for `y > 1`.
* `perron_lt_one` — `‖perronContour y c T‖ ≤ 2·yᶜ/(T·|log y|)` for `0 < y < 1`.
* `perron_trunc` — the packaged two-sided statement with the explicit constant.

All results are axiom-clean (`propext, Classical.choice, Quot.sound`); no
`native_decide`, no new axioms, no `sorry`.
-/

open MeasureTheory Complex Set intervalIntegral Filter Topology
open scoped BigOperators

noncomputable section
namespace Salt.MR
open Salt.SW

/-- The (discontinuous) Perron kernel `yˢ/s`. -/
def pk (y : ℝ) (s : ℂ) : ℂ := (y : ℂ) ^ s / s

/-- The truncated Perron contour integral value
`∫_{c−iT}^{c+iT} yˢ/s ds = I·∫_{−T}^T y^{c+it}/(c+it) dt`. -/
def perronContour (y c T : ℝ) : ℂ :=
  I * ∫ v in (-T)..T, pk y ((c : ℂ) + (v : ℂ) * I)

/-! ## Helper: the real geometric integral `∫ yˣ`. -/

/-- `∫_a^b yˣ dx = (yᵇ − yᵃ)/log y` for `y > 0`, `log y ≠ 0`. -/
lemma integral_rpow_base {y : ℝ} (hy : 0 < y) (hln : Real.log y ≠ 0) (a b : ℝ) :
    ∫ x in a..b, (y : ℝ) ^ x = ((y : ℝ) ^ b - (y : ℝ) ^ a) / Real.log y := by
  have hcont : Continuous (fun x : ℝ => (y : ℝ) ^ x) := by
    have hrw : (fun x : ℝ => (y : ℝ) ^ x) = fun x => Real.exp (Real.log y * x) := by
      funext x; rw [Real.rpow_def_of_pos hy]
    rw [hrw]; fun_prop
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => (y : ℝ) ^ x / Real.log y) ((y : ℝ) ^ x) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => (y : ℝ) ^ x) ((y : ℝ) ^ x * Real.log y) x :=
      (Real.hasStrictDerivAt_const_rpow hy x).hasDerivAt
    have h2 := h1.div_const (Real.log y)
    rwa [mul_div_assoc, div_self hln, mul_one] at h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a b),
    div_sub_div_same]

/-! ## Helper: the horizontal edge bound. -/

/-- A horizontal edge at fixed height `h` with `T ≤ |h|` (`T > 0`): its integral has
modulus `≤ (∫ yˣ)/T`, because `‖y^{x+hI}/(x+hI)‖ = yˣ/√(x²+h²) ≤ yˣ/T`. -/
lemma horiz_edge_norm {y : ℝ} (hy : 0 < y) {T h a b : ℝ} (hT : 0 < T) (hTh : T ≤ |h|)
    (hab : a ≤ b) :
    ‖∫ x in a..b, pk y ((x : ℂ) + (h : ℂ) * I)‖
      ≤ (∫ x in a..b, (y : ℝ) ^ x) / T := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hne : ∀ x : ℝ, ((x : ℂ) + (h : ℂ) * I) ≠ 0 := by
    intro x he
    have hpos : (0 : ℝ) < |h| := lt_of_lt_of_le hT hTh
    have hh0 : h = 0 := by
      have h1 : ((x : ℂ) + (h : ℂ) * I).im = h := by simp
      rw [he] at h1; simpa using h1.symm
    rw [hh0] at hpos; simp at hpos
  have hcont : Continuous (fun x : ℝ => pk y ((x : ℂ) + (h : ℂ) * I)) := by
    refine Continuous.div ?_ ?_ hne
    · exact (continuous_id.const_cpow (Or.inl hyC)).comp (by fun_prop)
    · fun_prop
  have hbd : ∀ x ∈ Set.Icc a b,
      ‖pk y ((x : ℂ) + (h : ℂ) * I)‖ ≤ (y : ℝ) ^ x / T := by
    intro x _
    rw [pk, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hre : ((x : ℂ) + (h : ℂ) * I).re = x := by simp
    rw [hre]
    have hnorm : T ≤ ‖(x : ℂ) + (h : ℂ) * I‖ := by
      rw [Complex.norm_add_mul_I, show T = √(T ^ 2) from (Real.sqrt_sq hT.le).symm]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x, sq_abs h, mul_self_le_mul_self hT.le hTh])
    have hnn : (0 : ℝ) ≤ (y : ℝ) ^ x := (Real.rpow_pos_of_pos hy x).le
    gcongr
  have hf_ii : IntervalIntegrable (fun x => ‖pk y ((x : ℂ) + (h : ℂ) * I)‖) volume a b :=
    hcont.norm.intervalIntegrable a b
  have hg_ii : IntervalIntegrable (fun x => (y : ℝ) ^ x / T) volume a b := by
    apply Continuous.intervalIntegrable
    have hrw : (fun x : ℝ => (y : ℝ) ^ x / T) = fun x => Real.exp (Real.log y * x) / T := by
      funext x; rw [Real.rpow_def_of_pos hy]
    rw [hrw]; fun_prop
  calc ‖∫ x in a..b, pk y ((x : ℂ) + (h : ℂ) * I)‖
      ≤ ∫ x in a..b, ‖pk y ((x : ℂ) + (h : ℂ) * I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ x in a..b, (y : ℝ) ^ x / T :=
        intervalIntegral.integral_mono_on hab hf_ii hg_ii hbd
    _ = (∫ x in a..b, (y : ℝ) ^ x) / T := intervalIntegral.integral_div T _

/-! ## Helper: the left/right vertical edge bound. -/

/-- A vertical edge at fixed real part `w` with `R ≤ |w|` (`R > 0`), over `Im ∈ [−T, T]`:
its integral has modulus `≤ 2T·y^w/R`, since
`‖y^{w+vI}/(w+vI)‖ = y^w/√(w²+v²) ≤ y^w/R`. -/
lemma vert_edge_norm {y : ℝ} (hy : 0 < y) {R T w : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hRw : R ≤ |w|) :
    ‖∫ v in (-T)..T, pk y ((w : ℂ) + (v : ℂ) * I)‖ ≤ 2 * T * ((y : ℝ) ^ w / R) := by
  have hbd : ∀ v ∈ Set.uIoc (-T) T,
      ‖pk y ((w : ℂ) + (v : ℂ) * I)‖ ≤ (y : ℝ) ^ w / R := by
    intro v _
    rw [pk, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hre : ((w : ℂ) + (v : ℂ) * I).re = w := by simp
    rw [hre]
    have hnorm : R ≤ ‖(w : ℂ) + (v : ℂ) * I‖ := by
      rw [Complex.norm_add_mul_I, show R = √(R ^ 2) from (Real.sqrt_sq hR.le).symm]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg v, sq_abs w, mul_self_le_mul_self hR.le hRw])
    have hnn : (0 : ℝ) ≤ (y : ℝ) ^ w := (Real.rpow_pos_of_pos hy w).le
    gcongr
  have hlen : |T - (-T)| = 2 * T := by
    rw [show T - -T = 2 * T by ring, abs_of_pos (by linarith)]
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  calc ‖∫ v in (-T)..T, pk y ((w : ℂ) + (v : ℂ) * I)‖
      ≤ (y : ℝ) ^ w / R * |T - (-T)| := hmain
    _ = 2 * T * ((y : ℝ) ^ w / R) := by rw [hlen]; ring

/-! ## The rectangle residue: `∮ yˢ/s = 2πi` (pole at `s = 0`, residue `1`). -/

/-- For `y > 0`, the boundary integral of `yˢ/s` over the rectangle
`[−R, c] × [−T, T]` (which strictly encloses the pole at `s = 0`) is `2πi`. -/
lemma pk_rect_residue {y : ℝ} (hy : 0 < y) {R T c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hT : 0 < T) :
    rectBI (((-R : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        (((c : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I) (pk y)
      = 2 * (Real.pi : ℂ) * I := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hφ : DifferentiableOn ℂ (fun s => (y : ℂ) ^ s)
      (closedRect (((-R : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        (((c : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I)) :=
    fun s _ => (differentiableAt_id.const_cpow (Or.inl hyC)).differentiableWithinAt
  have h := rectBI_cif_eq (φ := fun s => (y : ℂ) ^ s) (p := 0) hφ
    (by simp; linarith) (by simp; linarith)
    ⟨by simp; linarith, by simp; linarith⟩ ⟨by simp; linarith, by simp; linarith⟩
  simp only [sub_zero, Complex.cpow_zero, mul_one] at h
  rw [show pk y = fun s => (y : ℂ) ^ s / s from rfl]
  exact h

/-! ## R1 — the `y > 1` case. -/

/-- **Truncated Perron, `y > 1`.**  For `c > 0`, `T > 0`, `1 < y`,
`‖perronContour y c T − 2πi‖ ≤ 2·yᶜ/(T·log y)`.  The residue at `s = 0` contributes
`2πi`; the two horizontal edges of the left-closing rectangle carry the error, while
the left edge `Re = −R` is squeezed to `0` (explicit `R`). -/
theorem perron_gt_one {y c T : ℝ} (hy : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronContour y c T - 2 * (Real.pi : ℂ) * I‖
      ≤ 2 * ((y : ℝ) ^ c / (T * Real.log y)) := by
  have hy0 : 0 < y := lt_trans one_pos hy
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hlogne : Real.log y ≠ 0 := hlog.ne'
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  -- choose the horizontal extent `R`
  set R := max 1 (2 * T / (ε * Real.log y)) with hRdef
  have hR1 : (1 : ℝ) ≤ R := le_max_left _ _
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRbig : 2 * T / (ε * Real.log y) ≤ R := le_max_right _ _
  -- ∫_{-R}^c yˣ ≤ yᶜ/log y, hence the horizontal-edge value ≤ yᶜ/(T·log y)
  have hint_le : (∫ x in (-R)..c, (y : ℝ) ^ x) ≤ (y : ℝ) ^ c / Real.log y := by
    rw [integral_rpow_base hy0 hlogne, sub_div]
    have h0 : 0 ≤ (y : ℝ) ^ (-R) / Real.log y :=
      div_nonneg (Real.rpow_pos_of_pos hy0 _).le hlog.le
    linarith
  have hedge : (∫ x in (-R)..c, (y : ℝ) ^ x) / T ≤ (y : ℝ) ^ c / (T * Real.log y) := by
    rw [show (y : ℝ) ^ c / (T * Real.log y) = (y : ℝ) ^ c / Real.log y / T from by
      rw [mul_comm, ← div_div]]
    gcongr
  -- the rectangle identity, unfolded to the four edges
  have hres := pk_rect_residue hy0 hR0 hc hT
  have hunf : rectBI (((-R : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
      (((c : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I) (pk y)
      = (∫ x in (-R)..c, pk y ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
        - (∫ x in (-R)..c, pk y ((x : ℂ) + ((T : ℝ) : ℂ) * I))
        + I * (∫ v in (-T)..T, pk y ((c : ℂ) + (v : ℂ) * I))
        - I * (∫ v in (-T)..T, pk y (((-R : ℝ) : ℂ) + (v : ℂ) * I)) := by
    rw [rectBI]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, add_zero, mul_one, sub_zero, zero_add]
  rw [hunf] at hres
  -- perronContour − 2πi = TOP − BOTTOM + I·LEFT
  have hid : perronContour y c T - 2 * (Real.pi : ℂ) * I
      = (∫ x in (-R)..c, pk y ((x : ℂ) + ((T : ℝ) : ℂ) * I))
        - (∫ x in (-R)..c, pk y ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
        + I * (∫ v in (-T)..T, pk y (((-R : ℝ) : ℂ) + (v : ℂ) * I)) := by
    rw [show perronContour y c T
      = I * ∫ v in (-T)..T, pk y ((c : ℂ) + (v : ℂ) * I) from rfl]
    linear_combination hres
  -- edge bounds
  have hTOP : ‖∫ x in (-R)..c, pk y ((x : ℂ) + ((T : ℝ) : ℂ) * I)‖
      ≤ (y : ℝ) ^ c / (T * Real.log y) :=
    (horiz_edge_norm hy0 hT (le_abs_self T) (by linarith)).trans hedge
  have hBOT : ‖∫ x in (-R)..c, pk y ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
      ≤ (y : ℝ) ^ c / (T * Real.log y) :=
    (horiz_edge_norm hy0 hT (by rw [abs_neg]; exact le_abs_self T) (by linarith)).trans hedge
  have hLFT : ‖∫ v in (-T)..T, pk y (((-R : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ 2 * T * ((y : ℝ) ^ (-R) / R) :=
    vert_edge_norm hy0 hR0 hT (by rw [abs_neg]; exact le_abs_self R)
  have hIL : ‖I * (∫ v in (-T)..T, pk y (((-R : ℝ) : ℂ) + (v : ℂ) * I))‖
      = ‖∫ v in (-T)..T, pk y (((-R : ℝ) : ℂ) + (v : ℂ) * I)‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  -- the left edge is ≤ ε
  have hyR_ge : R * Real.log y ≤ (y : ℝ) ^ R := by
    rw [Real.rpow_def_of_pos hy0, mul_comm (Real.log y) R]
    linarith [Real.add_one_le_exp (R * Real.log y)]
  have hbound_ynegR : (y : ℝ) ^ (-R) ≤ 1 / (R * Real.log y) := by
    rw [Real.rpow_neg hy0.le, ← one_div]
    exact one_div_le_one_div_of_le (mul_pos hR0 hlog) hyR_ge
  have hεlog : 0 < ε * Real.log y := mul_pos hε hlog
  rw [div_le_iff₀ hεlog] at hRbig
  have key : 2 * T * ((y : ℝ) ^ (-R) / R) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ hR0]
    have hb1 : 2 * T * (y : ℝ) ^ (-R) ≤ 2 * T * (1 / (R * Real.log y)) := by
      gcongr
    have hb2 : 2 * T * (1 / (R * Real.log y)) ≤ ε * R := by
      rw [mul_one_div, div_le_iff₀ (mul_pos hR0 hlog)]
      nlinarith [hRbig, mul_nonneg (mul_nonneg (mul_nonneg hε.le hlog.le) hR0.le)
        (by linarith : (0 : ℝ) ≤ R - 1)]
    linarith
  -- assemble
  rw [hid]
  have htri : ‖(∫ x in (-R)..c, pk y ((x : ℂ) + ((T : ℝ) : ℂ) * I))
      - (∫ x in (-R)..c, pk y ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
      + I * (∫ v in (-T)..T, pk y (((-R : ℝ) : ℂ) + (v : ℂ) * I))‖
      ≤ ‖∫ x in (-R)..c, pk y ((x : ℂ) + ((T : ℝ) : ℂ) * I)‖
        + ‖∫ x in (-R)..c, pk y ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
        + ‖I * (∫ v in (-T)..T, pk y (((-R : ℝ) : ℂ) + (v : ℂ) * I))‖ := by
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_sub_le _ _
  linarith [htri, hTOP, hBOT, hLFT, hIL, key]

/-! ## The rectangle with no pole: `∮ yˢ/s = 0` (rectangle right of `Re = 0`). -/

/-- For `y > 0` and a rectangle `[c, R] × [−T, T]` with `0 < c` (so `s ≠ 0` throughout),
the boundary integral of `yˢ/s` is `0` (Cauchy–Goursat, no enclosed pole). -/
lemma pk_rect_zero {y : ℝ} (hy : 0 < y) {R T c : ℝ} (hcR : c < R) (hc : 0 < c) :
    rectBI (((c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        (((R : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I) (pk y)
      = 0 := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  apply rectBI_eq_zero_of_differentiableOn
  intro s hs
  rw [closedRect, Complex.mem_reProdIm] at hs
  have h1 : s.re ∈ Set.uIcc (((c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).re
      (((R : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I).re := hs.1
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] at h1
  rw [Set.uIcc_of_le hcR.le] at h1
  have hsre : 0 < s.re := lt_of_lt_of_le hc h1.1
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
  exact ((differentiableAt_id.const_cpow (Or.inl hyC)).div differentiableAt_id
    hs0).differentiableWithinAt

/-! ## R2 — the `0 < y < 1` case. -/

/-- **Truncated Perron, `0 < y < 1`.**  For `c > 0`, `T > 0`, `0 < y < 1`,
`‖perronContour y c T‖ ≤ 2·yᶜ/(T·|log y|)`.  The right-closing rectangle encloses no
pole (boundary `= 0`); the horizontal edges carry the error and the right edge
`Re = R` is squeezed to `0` (explicit `R`). -/
theorem perron_lt_one {y c T : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hc : 0 < c) (hT : 0 < T) :
    ‖perronContour y c T‖ ≤ 2 * ((y : ℝ) ^ c / (T * |Real.log y|)) := by
  have hlogneg : Real.log y < 0 := Real.log_neg hy0 hy1
  have hlogne : Real.log y ≠ 0 := hlogneg.ne
  set M := |Real.log y| with hMdef
  have hMpos : 0 < M := abs_pos.mpr hlogne
  have hlogM : Real.log y = -M := by rw [hMdef, abs_of_neg hlogneg]; ring
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  -- choose the horizontal extent `R` (needs `R > c`)
  set R := max (c + 1) (2 * T / (ε * M)) with hRdef
  have hRc1 : c + 1 ≤ R := le_max_left _ _
  have hcR : c < R := lt_of_lt_of_le (by linarith) hRc1
  have hR0 : 0 < R := lt_trans hc hcR
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hRbig : 2 * T / (ε * M) ≤ R := le_max_right _ _
  -- ∫_c^R yˣ ≤ yᶜ/M, hence the horizontal-edge value ≤ yᶜ/(T·M)
  have heq : (∫ x in c..R, (y : ℝ) ^ x) = ((y : ℝ) ^ c - (y : ℝ) ^ R) / M := by
    rw [integral_rpow_base hy0 hlogne, hlogM, div_neg, ← neg_div, neg_sub]
  have hint_le : (∫ x in c..R, (y : ℝ) ^ x) ≤ (y : ℝ) ^ c / M := by
    rw [heq, sub_div]
    have h0 : 0 ≤ (y : ℝ) ^ R / M := div_nonneg (Real.rpow_pos_of_pos hy0 _).le hMpos.le
    linarith
  have hedge : (∫ x in c..R, (y : ℝ) ^ x) / T ≤ (y : ℝ) ^ c / (T * M) := by
    rw [show (y : ℝ) ^ c / (T * M) = (y : ℝ) ^ c / M / T from by rw [mul_comm, ← div_div]]
    gcongr
  -- the rectangle identity (no pole), unfolded to the four edges
  have hres := pk_rect_zero (T := T) hy0 hcR hc
  have hunf : rectBI (((c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
      (((R : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I) (pk y)
      = (∫ x in c..R, pk y ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
        - (∫ x in c..R, pk y ((x : ℂ) + ((T : ℝ) : ℂ) * I))
        + I * (∫ v in (-T)..T, pk y ((R : ℂ) + (v : ℂ) * I))
        - I * (∫ v in (-T)..T, pk y ((c : ℂ) + (v : ℂ) * I)) := by
    rw [rectBI]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, add_zero, mul_one, sub_zero, zero_add]
  rw [hunf] at hres
  -- perronContour = BOTTOM − TOP + I·RIGHT
  have hid : perronContour y c T
      = (∫ x in c..R, pk y ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
        - (∫ x in c..R, pk y ((x : ℂ) + ((T : ℝ) : ℂ) * I))
        + I * (∫ v in (-T)..T, pk y ((R : ℂ) + (v : ℂ) * I)) := by
    rw [show perronContour y c T
      = I * ∫ v in (-T)..T, pk y ((c : ℂ) + (v : ℂ) * I) from rfl]
    linear_combination -hres
  -- edge bounds
  have hTOP : ‖∫ x in c..R, pk y ((x : ℂ) + ((T : ℝ) : ℂ) * I)‖
      ≤ (y : ℝ) ^ c / (T * M) :=
    (horiz_edge_norm hy0 hT (le_abs_self T) hcR.le).trans hedge
  have hBOT : ‖∫ x in c..R, pk y ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
      ≤ (y : ℝ) ^ c / (T * M) :=
    (horiz_edge_norm hy0 hT (by rw [abs_neg]; exact le_abs_self T) hcR.le).trans hedge
  have hRGT : ‖∫ v in (-T)..T, pk y ((R : ℂ) + (v : ℂ) * I)‖
      ≤ 2 * T * ((y : ℝ) ^ R / R) :=
    vert_edge_norm hy0 hR0 hT (le_abs_self R)
  have hIR : ‖I * (∫ v in (-T)..T, pk y ((R : ℂ) + (v : ℂ) * I))‖
      = ‖∫ v in (-T)..T, pk y ((R : ℂ) + (v : ℂ) * I)‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  -- the right edge is ≤ ε
  have hbound_yR : (y : ℝ) ^ R ≤ 1 / (R * M) := by
    rw [Real.rpow_def_of_pos hy0, show Real.log y * R = -(R * M) from by rw [hlogM]; ring,
      Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (mul_pos hR0 hMpos)
      (by linarith [Real.add_one_le_exp (R * M)])
  have hεM : 0 < ε * M := mul_pos hε hMpos
  rw [div_le_iff₀ hεM] at hRbig
  have key : 2 * T * ((y : ℝ) ^ R / R) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ hR0]
    have hb1 : 2 * T * (y : ℝ) ^ R ≤ 2 * T * (1 / (R * M)) := by gcongr
    have hb2 : 2 * T * (1 / (R * M)) ≤ ε * R := by
      rw [mul_one_div, div_le_iff₀ (mul_pos hR0 hMpos)]
      nlinarith [hRbig, mul_nonneg (mul_nonneg (mul_nonneg hε.le hMpos.le) hR0.le)
        (by linarith : (0 : ℝ) ≤ R - 1)]
    linarith
  -- assemble
  rw [hid]
  have htri : ‖(∫ x in c..R, pk y ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
      - (∫ x in c..R, pk y ((x : ℂ) + ((T : ℝ) : ℂ) * I))
      + I * (∫ v in (-T)..T, pk y ((R : ℂ) + (v : ℂ) * I))‖
      ≤ ‖∫ x in c..R, pk y ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
        + ‖∫ x in c..R, pk y ((x : ℂ) + ((T : ℝ) : ℂ) * I)‖
        + ‖I * (∫ v in (-T)..T, pk y ((R : ℂ) + (v : ℂ) * I))‖ := by
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_sub_le _ _
  linarith [htri, hTOP, hBOT, hRGT, hIR, key]

/-! ## R3 — the packaged two-sided truncated Perron formula. -/

/-- **Truncated Perron formula with explicit error** (Montgomery–Vaughan, Thm 5.1).
For `c > 0`, `T > 0`, `y > 0`, `y ≠ 1`,
`‖perronContour y c T − 2πi·𝟙(y>1)‖ ≤ 2·yᶜ/(T·|log y|)`,
where `perronContour y c T = ∫_{c−iT}^{c+iT} yˢ/s ds`.  Dividing by `2πi` gives the
classical `(1/2πi)∫ yˢ/s = 𝟙(y>1) + O(yᶜ/(T|log y|))` with an explicit constant. -/
theorem perron_trunc {y c T : ℝ} (hy0 : 0 < y) (hy1 : y ≠ 1) (hc : 0 < c) (hT : 0 < T) :
    ‖perronContour y c T - 2 * (Real.pi : ℂ) * I * (if 1 < y then (1 : ℂ) else 0)‖
      ≤ 2 * ((y : ℝ) ^ c / (T * |Real.log y|)) := by
  rcases lt_or_gt_of_ne hy1 with hlt | hgt
  · rw [if_neg (not_lt.mpr hlt.le), mul_zero, sub_zero]
    exact perron_lt_one hy0 hlt hc hT
  · rw [if_pos hgt, mul_one, abs_of_pos (Real.log_pos hgt)]
    exact perron_gt_one hgt hc hT

end Salt.MR
