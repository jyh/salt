/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The SW rung, wave S5 — the contour shift with residues-lite

Design: `docs/blueprints/sw.md`, wave S5. The classical contour shift moves the
S1b Perron line integral `Re s = c` into the S3 zero-free region and picks up the
poles (the `s = 1` pole of `−L'/L(χ₀)` and the exceptional real zero `β₁`) as
residues. mathlib has **no** residue theorem, so this module builds the
*residues-lite* core from mathlib's rectangle Cauchy–Goursat
(`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`) plus
the principal-part / `dslope` subtraction trick.

## Route (the residues-lite machinery)

Write `rectBI z w f` for the boundary integral of `f` over the rectangle with
opposite corners `z, w` (mathlib's orientation: bottom − top + `I`·right −
`I`·left).

1. **Goursat re-export** (`rectBI_eq_zero_of_differentiableOn`): if `f` is
   analytic on the closed rectangle, `rectBI z w f = 0`.
2. **The `dslope` trick** (`rectBI_dslope_eq_zero`): for `φ` analytic on the
   closed rectangle and an interior point `p`, the difference quotient
   `dslope φ p` is analytic *except possibly at `p`*, but Goursat's
   off-a-countable-set form (exceptional set `{p}`) still gives
   `rectBI z w (dslope φ p) = 0` — no need for `dslope`-differentiability at `p`.
3. **The rectangle CIF** (`rectBI_cif`): since `φ s/(s−p) = dslope φ p s + φ p /(s−p)`
   off `p`, additivity gives `rectBI z w (fun s => φ s/(s−p)) = φ p · W`, where
   `W := rectBI z w (fun s => (s−p)⁻¹)` is the **rectangle winding number**.
4. **The winding number** (`rectBI_inv_eq_two_pi_I`): `W = 2πi` for `p` strictly
   interior — the one piece mathlib lacks.  Built from the complex-log
   antiderivative `log(s−p)` of `(s−p)⁻¹` on each edge
   (`integral_eq_sub_of_hasDerivAt` + `HasDerivAt.clog_real`); the left edge
   crosses the branch cut, so there we use `log(p−s)` instead, and the mismatch
   is exactly the two branch jumps `log w − log(−w) = ±πi` that sum to `2πi`.
5. **The residue extraction** (`rectBI_cif_eq`): `∮ φ(s)/(s−p) = 2πi·φ(p)`; and
   **the kernel residue** (`kernel_residue`): the concrete payload for the S6
   assembly — `rectBI z w (fun s => x^{s+1}/(s(s+1)) / (s−β)) = 2πi·x^{β+1}/(β(β+1))`.

Scope note (PB-floor): this module lands the residues-lite core (steps 1–5 as they
close). The full `psi1_contour_shift` assembly (truncating the S1b line integral,
the four boundary estimates via the S2 partial fractions, and the `∃-T'`/`∃-σ₀'`
well-spacing dodges) consumes this core and is the remaining S5 work.

All results axiom-clean (`propext, Classical.choice, Quot.sound`); no
`native_decide`, no new axioms, no `sorry`.
-/

open Complex Set MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section
namespace Salt.SW

/-- **The rectangle boundary integral.** `rectBI z w f` is the integral of `f`
over the (counterclockwise-from-bottom) boundary of the axis-parallel rectangle
with opposite corners `z, w`, in mathlib's Cauchy–Goursat orientation:
bottom − top + `I`·right − `I`·left.  (For `z` lower-left and `w` upper-right this
is the counterclockwise boundary.) -/
def rectBI (z w : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
    + I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- The closed rectangle with opposite corners `z, w`. -/
def closedRect (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

/-- The open rectangle with opposite corners `z, w`. -/
def openRect (z w : ℂ) : Set ℂ :=
  Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)

lemma isOpen_openRect (z w : ℂ) : IsOpen (openRect z w) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

lemma openRect_subset_closedRect (z w : ℂ) : openRect z w ⊆ closedRect z w := by
  intro s hs
  obtain ⟨hre, him⟩ := hs
  exact ⟨Set.Ioo_subset_Icc_self hre, Set.Ioo_subset_Icc_self him⟩

/-- The closed rectangle is a neighbourhood of every interior (open-rectangle) point. -/
lemma closedRect_mem_nhds {z w p : ℂ} (hp : p ∈ openRect z w) : closedRect z w ∈ 𝓝 p :=
  Filter.mem_of_superset ((isOpen_openRect z w).mem_nhds hp) (openRect_subset_closedRect z w)

/-! ## 1. Cauchy–Goursat re-exports -/

/-- **Cauchy–Goursat for a rectangle, off a countable set.**  If `f` is continuous on the
closed rectangle and complex-differentiable on the open rectangle except at a countable set `s`,
then its boundary integral vanishes.  (Direct re-export of mathlib's
`integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`; `I •` becomes `I *` on `ℂ`.) -/
lemma rectBI_eq_zero_off_countable {z w : ℂ} {f : ℂ → ℂ} {s : Set ℂ} (hs : s.Countable)
    (Hc : ContinuousOn f (closedRect z w))
    (Hd : ∀ p ∈ openRect z w \ s, DifferentiableAt ℂ f p) :
    rectBI z w f = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w s hs
    Hc Hd
  simpa only [rectBI, smul_eq_mul] using h

/-- **Cauchy–Goursat for a rectangle.**  If `f` is analytic on the closed rectangle, its boundary
integral vanishes. -/
lemma rectBI_eq_zero_of_differentiableOn {z w : ℂ} {f : ℂ → ℂ}
    (H : DifferentiableOn ℂ f (closedRect z w)) : rectBI z w f = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w H
  simpa only [rectBI, smul_eq_mul] using h

/-! ## 2. The `dslope` principal-part trick -/

/-- **The `dslope` Goursat vanishing.**  For `φ` analytic on the closed rectangle and an interior
point `p`, the difference quotient `dslope φ p` (which equals `(φ ·−φ p)/(·−p)` off `p` and
`deriv φ p` at `p`) is analytic on the open rectangle *except possibly at `p`* — and it is
continuous through `p`.  So Goursat's off-a-countable-set form (exceptional set `{p}`) gives a
vanishing boundary integral without ever needing `dslope`-differentiability at `p`. -/
lemma rectBI_dslope_eq_zero {z w p : ℂ} {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ (closedRect z w)) (hp : p ∈ openRect z w) :
    rectBI z w (dslope φ p) = 0 := by
  have hpc : closedRect z w ∈ 𝓝 p := closedRect_mem_nhds hp
  have hφp : DifferentiableAt ℂ φ p := hφ.differentiableAt hpc
  refine rectBI_eq_zero_off_countable (s := {p}) (countable_singleton p) ?_ ?_
  · exact (continuousOn_dslope hpc).mpr ⟨hφ.continuousOn, hφp⟩
  · intro x hx
    have hxp : x ≠ p := fun h => hx.2 (mem_singleton_iff.mpr h)
    exact (differentiableAt_dslope_of_ne hxp).mpr (hφ.differentiableAt (closedRect_mem_nhds hx.1))

/-! ## 3. The rectangle Cauchy integral formula (up to the winding number) -/

/-- **Edge split.**  Along one edge (parametrised by `t ↦ γ t` for `t ∈ [a,b]`), the integrand
`φ(γ t)/(γ t − p)` splits as `dslope φ p (γ t) + φ p·(γ t − p)⁻¹`.  Given interval-integrability of
the two pieces and the pointwise identity on the edge, the edge integral splits additively. -/
private lemma edge_split {a b : ℝ} {F g h : ℝ → ℂ} (φp : ℂ)
    (hg : IntervalIntegrable g volume a b) (hh : IntervalIntegrable h volume a b)
    (hpt : Set.EqOn F (fun t => g t + φp * h t) (Set.uIcc a b)) :
    (∫ t in a..b, F t) = (∫ t in a..b, g t) + φp * ∫ t in a..b, h t := by
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_add hg (hh.const_mul φp), intervalIntegral.integral_const_mul]

/-- **One rectangle edge.**  For an edge `γ` (globally continuous) mapping the parameter interval
into the closed rectangle and avoiding the pole `p`, the edge integral of `φ(·)/(·−p)` splits as
`∫ dslope φ p (γ) + φ p · ∫ (γ−p)⁻¹`. -/
private lemma rect_edge {z w p : ℂ} {φ : ℂ → ℂ} {a b : ℝ}
    (hds : ContinuousOn (dslope φ p) (closedRect z w))
    (γ : ℝ → ℂ) (hγ : Continuous γ)
    (hmaps : Set.MapsTo γ (Set.uIcc a b) (closedRect z w))
    (hne : ∀ t ∈ Set.uIcc a b, γ t ≠ p) :
    (∫ t in a..b, φ (γ t) / (γ t - p))
      = (∫ t in a..b, dslope φ p (γ t)) + φ p * ∫ t in a..b, (γ t - p)⁻¹ := by
  refine edge_split (φ p) ((hds.comp hγ.continuousOn hmaps).intervalIntegrable)
    (((hγ.continuousOn.sub continuousOn_const).inv₀
      (fun t ht => sub_ne_zero.mpr (hne t ht))).intervalIntegrable) ?_
  intro t ht
  have hd : γ t - p ≠ 0 := sub_ne_zero.mpr (hne t ht)
  change φ (γ t) / (γ t - p) = dslope φ p (γ t) + φ p * (γ t - p)⁻¹
  rw [dslope_of_ne φ (hne t ht), slope_def_field]
  field_simp
  ring

/-- **The rectangle Cauchy integral formula, up to the winding number.**  For `φ` analytic on the
closed rectangle with opposite corners `z` (lower-left) and `w` (upper-right), and `p` strictly
interior, the boundary integral of `φ(s)/(s−p)` equals `φ p` times the rectangle winding number
`W := rectBI z w (·−p)⁻¹`.  (Combined with `rectBI_inv_eq_two_pi_I` this is the residue extraction
`= 2πi·φ p`.)  Proof: `φ(s)/(s−p) = dslope φ p s + φ p·(s−p)⁻¹` off `p`, so additivity plus the
`dslope` Goursat vanishing (`rectBI_dslope_eq_zero`) collapse the boundary integral. -/
theorem rectBI_cif {z w p : ℂ} {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ (closedRect z w))
    (hzw_re : z.re < w.re) (hzw_im : z.im < w.im)
    (hp_re : z.re < p.re ∧ p.re < w.re) (hp_im : z.im < p.im ∧ p.im < w.im) :
    rectBI z w (fun s => φ s / (s - p)) = φ p * rectBI z w (fun s => (s - p)⁻¹) := by
  -- interior membership
  have hp : p ∈ openRect z w := by
    rw [openRect, mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo,
      min_eq_left hzw_re.le, max_eq_right hzw_re.le,
      min_eq_left hzw_im.le, max_eq_right hzw_im.le]
    exact ⟨hp_re, hp_im⟩
  have hpc : closedRect z w ∈ 𝓝 p := closedRect_mem_nhds hp
  have hφc : ContinuousOn φ (closedRect z w) := hφ.continuousOn
  have hds : ContinuousOn (dslope φ p) (closedRect z w) :=
    (continuousOn_dslope hpc).mpr ⟨hφc, hφ.differentiableAt hpc⟩
  -- membership of an edge point in the closed rectangle
  have hmem : ∀ {x y : ℝ}, x ∈ Set.uIcc z.re w.re → y ∈ Set.uIcc z.im w.im →
      (↑x + ↑y * I) ∈ closedRect z w := by
    intro x y hx hy
    rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · simpa using hx
    · simpa using hy
  -- the ≠-p facts on each edge (interior point differs from every edge in one coordinate)
  have hbot : ∀ t ∈ Set.uIcc z.re w.re, (↑t + ↑z.im * I : ℂ) ≠ p := fun t _ he => by
    have h2 := congrArg Complex.im he; simp at h2; linarith [hp_im.1]
  have htop : ∀ t ∈ Set.uIcc z.re w.re, (↑t + ↑w.im * I : ℂ) ≠ p := fun t _ he => by
    have h2 := congrArg Complex.im he; simp at h2; linarith [hp_im.2]
  have hrgt : ∀ t ∈ Set.uIcc z.im w.im, (↑w.re + ↑t * I : ℂ) ≠ p := fun t _ he => by
    have h2 := congrArg Complex.re he; simp at h2; linarith [hp_re.2]
  have hlft : ∀ t ∈ Set.uIcc z.im w.im, (↑z.re + ↑t * I : ℂ) ≠ p := fun t _ he => by
    have h2 := congrArg Complex.re he; simp at h2; linarith [hp_re.1]
  -- the four edge splits
  have Ebot := rect_edge hds (fun x => ↑x + ↑z.im * I) (by fun_prop)
    (fun x hx => hmem hx left_mem_uIcc) hbot
  have Etop := rect_edge hds (fun x => ↑x + ↑w.im * I) (by fun_prop)
    (fun x hx => hmem hx right_mem_uIcc) htop
  have Ergt := rect_edge hds (fun y => ↑w.re + ↑y * I) (by fun_prop)
    (fun y hy => hmem right_mem_uIcc hy) hrgt
  have Elft := rect_edge hds (fun y => ↑z.re + ↑y * I) (by fun_prop)
    (fun y hy => hmem left_mem_uIcc hy) hlft
  -- the `dslope` Goursat vanishing, unfolded to the edge integrals
  have h0 := rectBI_dslope_eq_zero hφ hp
  simp only [rectBI] at h0 ⊢
  rw [Ebot, Etop, Ergt, Elft]
  linear_combination h0

/-! ## 4. The rectangle winding number `∮_{∂R} (s−p)⁻¹ = 2πi` -/

/-- Branch-cut jump (upper): for `Im w > 0`, `log w − log (−w) = π i` (both moduli equal, and
`arg(−w) = arg w − π`). -/
private lemma log_sub_log_neg_im_pos {w : ℂ} (hw : 0 < w.im) :
    Complex.log w - Complex.log (-w) = ↑Real.pi * I := by
  apply Complex.ext
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw]

/-- Branch-cut jump (lower): for `Im w < 0`, `log w − log (−w) = −(π i)`. -/
private lemma log_sub_log_neg_im_neg {w : ℂ} (hw : w.im < 0) :
    Complex.log w - Complex.log (-w) = -(↑Real.pi * I) := by
  apply Complex.ext
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hw]

/-- Horizontal edge of the winding integral (fixed imaginary part `yc`): the complex-log
antiderivative `log(s−p)` is valid since the edge stays off the branch cut. -/
private lemma winding_horiz (yc : ℝ) (p : ℂ) {a b : ℝ}
    (hs : ∀ t ∈ Set.uIcc a b, ((↑t + ↑yc * I) - p) ∈ slitPlane) :
    (∫ t in a..b, ((↑t + ↑yc * I) - p)⁻¹)
      = Complex.log ((↑b + ↑yc * I) - p) - Complex.log ((↑a + ↑yc * I) - p) := by
  have hcont : ContinuousOn (fun t : ℝ => ((↑t + ↑yc * I) - p)⁻¹) (Set.uIcc a b) :=
    ContinuousOn.inv₀
      ((Complex.continuous_ofReal.add continuous_const).sub continuous_const).continuousOn
      (fun t ht => slitPlane_ne_zero (hs t ht))
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.log ((↑t + ↑yc * I) - p)) (((↑t + ↑yc * I) - p)⁻¹) t := by
    intro t ht
    have e : HasDerivAt (fun v : ℂ => (v + ↑yc * I) - p) 1 (↑t : ℂ) := by
      simpa using ((hasDerivAt_id (↑t : ℂ)).add_const (↑yc * I)).sub_const p
    have h := (e.comp_ofReal).clog_real (hs t ht)
    rwa [one_div] at h
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- Right vertical edge (fixed real part `xc`), non-crossing branch `log(s−p)`. -/
private lemma winding_vert (xc : ℝ) (p : ℂ) {a b : ℝ}
    (hs : ∀ t ∈ Set.uIcc a b, ((↑xc + ↑t * I) - p) ∈ slitPlane) :
    (∫ t in a..b, ((↑xc + ↑t * I) - p)⁻¹) * I
      = Complex.log ((↑xc + ↑b * I) - p) - Complex.log ((↑xc + ↑a * I) - p) := by
  have hcont : ContinuousOn (fun t : ℝ => ((↑xc + ↑t * I) - p)⁻¹ * I) (Set.uIcc a b) :=
    (ContinuousOn.inv₀
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const).continuousOn
      (fun t ht => slitPlane_ne_zero (hs t ht))).mul continuousOn_const
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.log ((↑xc + ↑t * I) - p))
        (((↑xc + ↑t * I) - p)⁻¹ * I) t := by
    intro t ht
    have e : HasDerivAt (fun v : ℂ => (↑xc + v * I) - p) I (↑t : ℂ) := by
      simpa using (((hasDerivAt_id (↑t : ℂ)).mul_const I).const_add (↑xc : ℂ)).sub_const p
    have h := (e.comp_ofReal).clog_real (hs t ht)
    rwa [div_eq_inv_mul] at h
  rw [← intervalIntegral.integral_mul_const]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- Left vertical edge (fixed real part `xc`): the edge crosses the branch cut of `log(s−p)`, so
we use the branch `log(p−s)` (valid there), whose derivative coincides with `(s−p)⁻¹·I`. -/
private lemma winding_vert_left (xc : ℝ) (p : ℂ) {a b : ℝ}
    (hs : ∀ t ∈ Set.uIcc a b, (p - (↑xc + ↑t * I)) ∈ slitPlane) :
    (∫ t in a..b, ((↑xc + ↑t * I) - p)⁻¹) * I
      = Complex.log (p - (↑xc + ↑b * I)) - Complex.log (p - (↑xc + ↑a * I)) := by
  have hne : ∀ t ∈ Set.uIcc a b, ((↑xc + ↑t * I) - p) ≠ 0 := fun t ht h =>
    slitPlane_ne_zero (hs t ht)
      (by rw [show p - (↑xc + ↑t * I) = -(((↑xc + ↑t * I) - p)) by ring, h, neg_zero])
  have hcont : ContinuousOn (fun t : ℝ => ((↑xc + ↑t * I) - p)⁻¹ * I) (Set.uIcc a b) :=
    (ContinuousOn.inv₀
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const).continuousOn hne).mul continuousOn_const
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.log (p - (↑xc + ↑t * I)))
        (((↑xc + ↑t * I) - p)⁻¹ * I) t := by
    intro t ht
    have e : HasDerivAt (fun v : ℂ => p - (↑xc + v * I)) (-I) (↑t : ℂ) := by
      simpa using (((hasDerivAt_id (↑t : ℂ)).mul_const I).const_add (↑xc : ℂ)).const_sub p
    have h := (e.comp_ofReal).clog_real (hs t ht)
    have hEq : (p - (↑xc + ↑t * I))⁻¹ * (-I) = ((↑xc + ↑t * I) - p)⁻¹ * I := by
      rw [show p - (↑xc + ↑t * I) = -(((↑xc + ↑t * I) - p)) by ring, inv_neg]; ring
    rw [div_eq_inv_mul, hEq] at h
    exact h
  rw [← intervalIntegral.integral_mul_const]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- **The rectangle winding number.**  For a strictly interior point `p`, the boundary integral of
`(s−p)⁻¹` around the rectangle is `2πi`.  Built from the complex-log antiderivative on each edge
(`winding_horiz`/`winding_vert`) — with the branch-cut-crossing left edge handled via `log(p−s)`
(`winding_vert_left`) — and the two branch jumps `log w − log(−w) = ±πi`.  mathlib has no residue
theorem, so this is the one piece the residues-lite core supplies by hand. -/
theorem rectBI_inv_eq_two_pi_I {z w p : ℂ}
    (hp_re : z.re < p.re ∧ p.re < w.re) (hp_im : z.im < p.im ∧ p.im < w.im) :
    rectBI z w (fun s => (s - p)⁻¹) = 2 * ↑Real.pi * I := by
  -- imaginary/real parts of the edge points (minus `p`)
  have him : ∀ (t yc : ℝ), ((↑t + ↑yc * I) - p).im = yc - p.im := fun t yc => by simp
  have hre : ∀ (xc t : ℝ), ((↑xc + ↑t * I) - p).re = xc - p.re := fun xc t => by simp
  have hreL : ∀ (xc t : ℝ), (p - (↑xc + ↑t * I)).re = p.re - xc := fun xc t => by simp
  -- slit-plane membership on each edge
  have hs_bot : ∀ t ∈ Set.uIcc z.re w.re, ((↑t + ↑z.im * I) - p) ∈ slitPlane := fun t _ =>
    mem_slitPlane_iff.mpr (Or.inr (by rw [him]; intro h; linarith [hp_im.1]))
  have hs_top : ∀ t ∈ Set.uIcc z.re w.re, ((↑t + ↑w.im * I) - p) ∈ slitPlane := fun t _ =>
    mem_slitPlane_iff.mpr (Or.inr (by rw [him]; intro h; linarith [hp_im.2]))
  have hs_rgt : ∀ t ∈ Set.uIcc z.im w.im, ((↑w.re + ↑t * I) - p) ∈ slitPlane := fun t _ =>
    mem_slitPlane_iff.mpr (Or.inl (by rw [hre]; linarith [hp_re.2]))
  have hs_lft : ∀ t ∈ Set.uIcc z.im w.im, (p - (↑z.re + ↑t * I)) ∈ slitPlane := fun t _ =>
    mem_slitPlane_iff.mpr (Or.inl (by rw [hreL]; linarith [hp_re.1]))
  -- the four edge evaluations
  have Ebot := winding_horiz z.im p hs_bot
  have Etop := winding_horiz w.im p hs_top
  have Ergt := winding_vert w.re p hs_rgt
  have Elft := winding_vert_left z.re p hs_lft
  -- branch jumps at the two left corners
  have hbTL : Complex.log ((↑z.re + ↑w.im * I) - p) - Complex.log (-((↑z.re + ↑w.im * I) - p))
      = ↑Real.pi * I := log_sub_log_neg_im_pos (by rw [him]; linarith [hp_im.2])
  have hbBL : Complex.log ((↑z.re + ↑z.im * I) - p) - Complex.log (-((↑z.re + ↑z.im * I) - p))
      = -(↑Real.pi * I) := log_sub_log_neg_im_neg (by rw [him]; linarith [hp_im.1])
  -- rewrite `p − s` corners in `Elft` to `−(s − p)` to match the branch jumps
  rw [show p - (↑z.re + ↑w.im * I) = -(((↑z.re + ↑w.im * I) - p)) by ring,
      show p - (↑z.re + ↑z.im * I) = -(((↑z.re + ↑z.im * I) - p)) by ring] at Elft
  -- assemble
  simp only [rectBI]
  rw [Ebot, Etop, mul_comm I _, mul_comm I _, Ergt, Elft]
  linear_combination hbTL - hbBL

/-! ## 5. The residue extraction and the kernel residue -/

/-- **The rectangle residue extraction.**  Combining the CIF (`rectBI_cif`) with the winding number
(`rectBI_inv_eq_two_pi_I`): for `φ` analytic on the closed rectangle and `p` strictly interior,
`∮_{∂R} φ(s)/(s−p) ds = 2πi·φ(p)`.  This is the residue theorem for a simple pole with residue
`φ(p)` — exactly the object the S5 contour shift needs to extract the exceptional-zero term. -/
theorem rectBI_cif_eq {z w p : ℂ} {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ (closedRect z w))
    (hzw_re : z.re < w.re) (hzw_im : z.im < w.im)
    (hp_re : z.re < p.re ∧ p.re < w.re) (hp_im : z.im < p.im ∧ p.im < w.im) :
    rectBI z w (fun s => φ s / (s - p)) = 2 * ↑Real.pi * I * φ p := by
  rw [rectBI_cif hφ hzw_re hzw_im hp_re hp_im, rectBI_inv_eq_two_pi_I hp_re hp_im]
  ring

/-- **The kernel residue** (the S5/S6 payload).  For `x > 0` and a rectangle strictly to the right
of the imaginary axis (`0 < z.re`, so `s`, `s+1 ≠ 0` throughout), the boundary integral of the
smoothed Perron kernel `x^{s+1}/(s(s+1))` against `1/(s−β)` picks up the residue at an interior
`β`:
`∮_{∂R} x^{s+1}/(s(s+1)) · 1/(s−β) ds = 2πi · x^{β+1}/(β(β+1))`.
This is the exceptional-zero main term the contour shift extracts (the S1b kernel is
`x^{s+1}/(s(s+1))`; near a simple zero `β` the factor `−L'/L` contributes the `1/(s−β)`). -/
theorem kernel_residue {z w : ℂ} {x : ℝ} (hx : 0 < x) {β : ℂ}
    (hz0 : 0 < z.re) (hzw_re : z.re < w.re) (hzw_im : z.im < w.im)
    (hβ_re : z.re < β.re ∧ β.re < w.re) (hβ_im : z.im < β.im ∧ β.im < w.im) :
    rectBI z w (fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - β))
      = 2 * ↑Real.pi * I * ((x : ℂ) ^ (β + 1) / (β * (β + 1))) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hφ : DifferentiableOn ℂ (fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1))) (closedRect z w) := by
    intro s hs
    have hsre : 0 < s.re := by
      have hmem : s.re ∈ Set.Icc z.re w.re := by
        rw [← Set.uIcc_of_le hzw_re.le]; exact hs.1
      exact lt_of_lt_of_le hz0 hmem.1
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
    have hs1 : s + 1 ≠ 0 := fun h => by
      have : (s + 1).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.one_re] at this; linarith
    have hd : DifferentiableAt ℂ (fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1))) s := by
      apply DifferentiableAt.div
      · exact (differentiableAt_id.add_const 1).const_cpow (Or.inl hxC)
      · exact differentiableAt_id.mul (differentiableAt_id.add_const 1)
      · exact mul_ne_zero hs0 hs1
    exact hd.differentiableWithinAt
  exact rectBI_cif_eq hφ hzw_re hzw_im hβ_re hβ_im

end Salt.SW
end
