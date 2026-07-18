/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.DHRepulsion
import Salt.SW.ContourShift

/-!
# The Deuring–Heilbronn contour: M3 residual pieces (HB-ENGINE, WP2, node DH-2b-iii)

Design: `docs/exploration/s3-hb3-design.md`, "DH-2b — THE PRODUCT-DETECTOR FREEZE".
Source: Benlİ–Goel–Twiss–Zaman, *Explicit Deuring–Heilbronn phenomenon for Dirichlet
L-functions* (arXiv:2410.06082), §§4–5.

This module builds the three residual M3 pieces of the landed `DHRepulsion` (`DH-2b-ii`),
keyed to the closing docstring of that module. The unshifted Mellin representation
(`dhDetector_mellin`) and the positivity floor (`dhDetector_floor`) are LANDED there; here
we supply the contour-side upper estimate ingredients:

* **M3-1 — the additive ζ Laurent split** (LANDED, `zetaHol`, `riemannZeta_eq_add_zetaHol`): the
  removable-singularity extraction `ζ(s) = 1/(s−1) + zetaHol s` with `zetaHol` entire (value `γ`
  at `1`). The ADDITIVE companion to the corpus's MULTIPLICATIVE `Zc = (s−1)·ζ`
  (`ZetaPartialFractions`), it is the exact "missing step" the predecessor named (item 1). It
  feeds the simple-pole residue machinery `ContourShift.rectBI_cif_eq` (`1/(s−β)`-shaped) to
  give the CLOSED residue payloads:
  * `rectBI_zeta_mul`: `∮_{∂R} ζ(s)·H(s) ds = 2πi·H(1)` (general cofactor `H`);
  * `rectBI_zeta_shift_mul`: `∮_{∂R} ζ(s+ρ)·H(s) ds = 2πi·H(1−ρ)` (the DH shift by a zero `ρ`);
  * `rectBI_zeta_LFunction_kernel`: the concrete DH main term
    `∮_{∂R} ζ·L(·,χ)·x^{s+1}/(s(s+1)) ds = 2πi·L(1,χ)·x²/2` — the `L(1,χ)`-carrying competing
    term of the DH balance the floor `dhDetector_floor` competes against.
* **M3-3 — the shifted-line bound `J`** (NAMED OBSTRUCTION, see closing docstring): the bulk.
* **M3-2 — the rectangle close** (NAMED OBSTRUCTION, see closing docstring): `rectBI` shift.

## Honesty / death map (HB-ENGINE, R4 — NO twin claim)

NOT a proof of the Twin Prime Conjecture. Delivers competing-estimate substrate for the
conditional `InfinitelyManySiegelZeros → TwinPrimeConjecture`; the death rung is R4.
-/

open Finset MeasureTheory Complex Filter
open scoped Topology

noncomputable section

namespace Salt.SW

/-! ## M3-1 — the additive ζ Laurent split `ζ(s) = 1/(s−1) + zetaHol s`

The `ζ`-pole at `s = 1` is the source of the `L(1,χ)`-carrying residue in `F = ζ·L`. The
`ContourShift` residue theorems (`rectBI_cif_eq`, `kernel_residue`) extract a residue from a
`φ(s)/(s−β)` shape with `φ` holomorphic across `β`. So we must first isolate the pole
ADDITIVELY: `ζ(s) = 1/(s−1) + zetaHol s`, whence `F(s) = L(s,χ)/(s−1) + zetaHol(s)·L(s,χ)`,
the first summand feeding the residue machinery with `φ = L(·,χ)·(kernel)` (residue
`L(1,χ)·kernel(1)`), the second holomorphic at `1`.

`zetaHol s := ζ(s) − 1/(s−1)`, extended across `s = 1` by its limit — the Euler–Mascheroni
constant `γ` (`Mathlib.tendsto_riemannZeta_sub_one_div`) — so the removable singularity makes
it differentiable at `1`. Mirrors the corpus `Zc` removable-singularity pattern
(`ZetaPartialFractions.Zc_analyticAt_one`). -/

/-- The holomorphic part of `ζ` at its simple pole: `zetaHol s = ζ(s) − 1/(s−1)`, extended
across `s = 1` by its limit `γ` (the Euler–Mascheroni constant). Entire (M3-1). -/
def zetaHol : ℂ → ℂ :=
  Function.update (fun s => riemannZeta s - 1 / (s - 1)) 1 (Real.eulerMascheroniConstant : ℂ)

lemma zetaHol_of_ne {s : ℂ} (hs : s ≠ 1) : zetaHol s = riemannZeta s - 1 / (s - 1) :=
  Function.update_of_ne hs _ _

lemma zetaHol_one : zetaHol 1 = (Real.eulerMascheroniConstant : ℂ) :=
  Function.update_self 1 _ _

/-- **M3-1 — the additive Laurent split.** For `s ≠ 1`, `ζ(s) = 1/(s−1) + zetaHol s`. -/
lemma riemannZeta_eq_add_zetaHol {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = 1 / (s - 1) + zetaHol s := by
  rw [zetaHol_of_ne hs]; ring

/-- `zetaHol` is continuous at the pole `s = 1` (the removable singularity, limit `γ`). -/
lemma zetaHol_continuousAt_one : ContinuousAt zetaHol 1 := by
  rw [← continuousWithinAt_compl_self]
  have hEq : (fun s => riemannZeta s - 1 / (s - 1)) =ᶠ[𝓝[≠] 1] zetaHol := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (zetaHol_of_ne hz).symm
  have h : Tendsto zetaHol (𝓝[≠] 1) (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
    tendsto_riemannZeta_sub_one_div.congr' hEq
  simpa [ContinuousWithinAt, zetaHol_one] using h

lemma zetaHol_differentiableAt_of_ne {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ zetaHol s := by
  have hraw : DifferentiableAt ℂ (fun z => riemannZeta z - 1 / (z - 1)) s :=
    (differentiableAt_riemannZeta hs).sub
      ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs))
  have hloc : zetaHol =ᶠ[𝓝 s] (fun z => riemannZeta z - 1 / (z - 1)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
    exact zetaHol_of_ne (by simpa using hz)
  exact hraw.congr_of_eventuallyEq hloc

lemma zetaHol_analyticAt_one : AnalyticAt ℂ zetaHol 1 := by
  apply analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ zetaHol_continuousAt_one
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact zetaHol_differentiableAt_of_ne hz

/-- **M3-1 — `zetaHol` is entire.** The removable singularity at `1` (value `γ`) makes the
naive difference `ζ − 1/(·−1)` differentiable everywhere. -/
lemma zetaHol_differentiableAt (s : ℂ) : DifferentiableAt ℂ zetaHol s := by
  rcases eq_or_ne s 1 with rfl | hs
  · exact zetaHol_analyticAt_one.differentiableAt
  · exact zetaHol_differentiableAt_of_ne hs

lemma zetaHol_differentiable : Differentiable ℂ zetaHol := zetaHol_differentiableAt

/-! ## M3-1 — the pole-extracting form of `F(s) = ζ(s)·L(s,χ)`

Feeding the residue machinery: `F` splits into a simple pole with holomorphic numerator
`L(·,χ)` (residue `L(1,χ)`) plus a term holomorphic at `1`. -/

/-- **M3-1 — the `F`-split.** For `s ≠ 1`, `ζ(s)·L(s,χ) = L(s,χ)/(s−1) + zetaHol(s)·L(s,χ)`.
The first summand is the simple pole feeding `rectBI_cif_eq` with numerator `L(·,χ)` (residue
`L(1,χ)`); the second is holomorphic at `1` (`zetaHol_LFunction_differentiableAt`). -/
lemma zeta_LFunction_split {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s * DirichletCharacter.LFunction χ s
      = DirichletCharacter.LFunction χ s / (s - 1)
        + zetaHol s * DirichletCharacter.LFunction χ s := by
  rw [riemannZeta_eq_add_zetaHol hs]; ring

/-- The holomorphic factor `zetaHol · L(·,χ)` of the split is differentiable everywhere
(for `χ ≠ 1`, `L(·,χ)` is entire; `zetaHol` is entire) — in particular at the pole `s = 1`,
so it contributes nothing to the residue. -/
lemma zetaHol_LFunction_differentiableAt {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (s : ℂ) :
    DifferentiableAt ℂ (fun z => zetaHol z * DirichletCharacter.LFunction χ z) s :=
  (zetaHol_differentiableAt s).mul (DirichletCharacter.differentiable_LFunction hχ s)

/-! ## M3-1 — the residue payload `∮_{∂R} ζ(s)·H(s) ds = 2πi·H(1)`

The concrete completion of the predecessor's "item 1" (the algebraic seam): with the pole
isolated additively (`riemannZeta_eq_add_zetaHol`), the rectangle boundary integral of
`ζ·H` extracts the `ζ`-pole residue `H(1)` for any cofactor `H` holomorphic on the rectangle.
Applied later with `H = L(·,χ)·G·(kernel)`, the residue is `L(1,χ)·G(1)·(kernel)(1)` — the
`L(1,χ)`-carrying competing term of the DH balance. -/

/-- **Boundary congruence.** Two integrands with the same values on `closedRect z w \ {p}`
(hence on the four edges, since `p` is strictly interior) have the same rectangle boundary
integral. (Edge-wise `intervalIntegral.integral_congr`; the interior point `p` never lies on
an edge.) -/
lemma rectBI_congr_boundary {z w p : ℂ} {f g : ℂ → ℂ}
    (hp_re : z.re < p.re ∧ p.re < w.re) (hp_im : z.im < p.im ∧ p.im < w.im)
    (h : Set.EqOn f g (closedRect z w \ {p})) :
    rectBI z w f = rectBI z w g := by
  have hmem : ∀ {x y : ℝ}, x ∈ Set.uIcc z.re w.re → y ∈ Set.uIcc z.im w.im →
      (↑x + ↑y * I) ∈ closedRect z w := by
    intro x y hx hy
    rw [closedRect, mem_reProdIm]
    exact ⟨by simpa using hx, by simpa using hy⟩
  have hbot : ∀ t ∈ Set.uIcc z.re w.re, (↑t + ↑z.im * I : ℂ) ≠ p := fun t _ he => by
    have h2 := congrArg Complex.im he; simp at h2; linarith [hp_im.1]
  have htop : ∀ t ∈ Set.uIcc z.re w.re, (↑t + ↑w.im * I : ℂ) ≠ p := fun t _ he => by
    have h2 := congrArg Complex.im he; simp at h2; linarith [hp_im.2]
  have hrgt : ∀ t ∈ Set.uIcc z.im w.im, (↑w.re + ↑t * I : ℂ) ≠ p := fun t _ he => by
    have h2 := congrArg Complex.re he; simp at h2; linarith [hp_re.2]
  have hlft : ∀ t ∈ Set.uIcc z.im w.im, (↑z.re + ↑t * I : ℂ) ≠ p := fun t _ he => by
    have h2 := congrArg Complex.re he; simp at h2; linarith [hp_re.1]
  have Ebot : (∫ x in z.re..w.re, f (↑x + ↑z.im * I)) = ∫ x in z.re..w.re, g (↑x + ↑z.im * I) :=
    intervalIntegral.integral_congr fun x hx =>
      h ⟨hmem hx (Set.left_mem_uIcc), hbot x hx⟩
  have Etop : (∫ x in z.re..w.re, f (↑x + ↑w.im * I)) = ∫ x in z.re..w.re, g (↑x + ↑w.im * I) :=
    intervalIntegral.integral_congr fun x hx =>
      h ⟨hmem hx (Set.right_mem_uIcc), htop x hx⟩
  have Ergt : (∫ y in z.im..w.im, f (↑w.re + ↑y * I)) = ∫ y in z.im..w.im, g (↑w.re + ↑y * I) :=
    intervalIntegral.integral_congr fun y hy =>
      h ⟨hmem (Set.right_mem_uIcc) hy, hrgt y hy⟩
  have Elft : (∫ y in z.im..w.im, f (↑z.re + ↑y * I)) = ∫ y in z.im..w.im, g (↑z.re + ↑y * I) :=
    intervalIntegral.integral_congr fun y hy =>
      h ⟨hmem (Set.left_mem_uIcc) hy, hlft y hy⟩
  simp only [rectBI]
  rw [Ebot, Etop, Ergt, Elft]

/-- **M3-1 residue payload.** For a cofactor `H` differentiable on the closed rectangle straddling
`s = 1` (`z.re < 1 < w.re`, `z.im < 0 < w.im`), the boundary integral of `ζ(s)·H(s)` extracts the
`ζ`-pole residue `H(1)`:  `∮_{∂R} ζ(s)·H(s) ds = 2πi·H(1)`.

Route: `ζ·H = φ/(s−1)` off `s = 1` for `φ s = H s + zetaHol(s)·H(s)·(s−1)` (holomorphic on the
rectangle since `zetaHol` and `H` are), so the boundary congruence reduces to
`rectBI_cif_eq` (`= 2πi·φ(1)`) and `φ 1 = H 1`. -/
theorem rectBI_zeta_mul {z w : ℂ} {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (closedRect z w))
    (hz_re : z.re < 1) (hw_re : 1 < w.re) (hz_im : z.im < 0) (hw_im : 0 < w.im) :
    rectBI z w (fun s => riemannZeta s * H s) = 2 * ↑Real.pi * I * H 1 := by
  have h1_re : z.re < (1 : ℂ).re ∧ (1 : ℂ).re < w.re := by rw [Complex.one_re]; exact ⟨hz_re, hw_re⟩
  have h1_im : z.im < (1 : ℂ).im ∧ (1 : ℂ).im < w.im := by rw [Complex.one_im]; exact ⟨hz_im, hw_im⟩
  have hzw_re : z.re < w.re := lt_trans hz_re hw_re
  have hzw_im : z.im < w.im := lt_trans hz_im hw_im
  set φ : ℂ → ℂ := fun s => H s + zetaHol s * H s * (s - 1) with hφdef
  have hφdiff : DifferentiableOn ℂ φ (closedRect z w) :=
    hH.add ((zetaHol_differentiable.differentiableOn.mul hH).mul
      ((differentiable_id.sub_const 1).differentiableOn))
  have hcongr : rectBI z w (fun s => riemannZeta s * H s)
      = rectBI z w (fun s => φ s / (s - 1)) := by
    refine rectBI_congr_boundary h1_re h1_im fun s hs => ?_
    have hs1 : s ≠ 1 := by simpa using hs.2
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    change riemannZeta s * H s = (H s + zetaHol s * H s * (s - 1)) / (s - 1)
    rw [riemannZeta_eq_add_zetaHol hs1]
    field_simp
  rw [hcongr, rectBI_cif_eq hφdiff hzw_re hzw_im h1_re h1_im, hφdef]
  simp

/-- **M3-1 — the SHIFTED residue (DH-ready).** The Deuring–Heilbronn detector is shifted by a zero
`ρ` of `L(·,χ)`: the integrand carries `ζ(s+ρ)`, whose pole is at `s = 1−ρ`. For `H` differentiable
on a rectangle straddling `s = 1−ρ`,

`∮_{∂R} ζ(s+ρ)·H(s) ds = 2πi · H(1−ρ)`.

This is the general shifted pole term (Benli Prop 5.1, item 1 of the predecessor's map); applied
with `H = L(·,χ)·G·(shifted kernel)` the residue is `L(1,χ)·G(1−ρ)·(kernel)(1−ρ)`. The unshifted
`rectBI_zeta_mul` is the `ρ = 0` case. -/
theorem rectBI_zeta_shift_mul {z w : ℂ} {ρ : ℂ} {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (closedRect z w))
    (hp_re : z.re < (1 - ρ).re ∧ (1 - ρ).re < w.re)
    (hp_im : z.im < (1 - ρ).im ∧ (1 - ρ).im < w.im) :
    rectBI z w (fun s => riemannZeta (s + ρ) * H s) = 2 * ↑Real.pi * I * H (1 - ρ) := by
  have hzw_re : z.re < w.re := lt_trans hp_re.1 hp_re.2
  have hzw_im : z.im < w.im := lt_trans hp_im.1 hp_im.2
  have hshift : DifferentiableOn ℂ (fun s => zetaHol (s + ρ)) (closedRect z w) :=
    (zetaHol_differentiable.comp (differentiable_id.add_const ρ)).differentiableOn
  set φ : ℂ → ℂ := fun s => H s + zetaHol (s + ρ) * H s * (s - (1 - ρ)) with hφdef
  have hφdiff : DifferentiableOn ℂ φ (closedRect z w) :=
    hH.add ((hshift.mul hH).mul ((differentiable_id.sub_const (1 - ρ)).differentiableOn))
  have hcongr : rectBI z w (fun s => riemannZeta (s + ρ) * H s)
      = rectBI z w (fun s => φ s / (s - (1 - ρ))) := by
    refine rectBI_congr_boundary hp_re hp_im fun s hs => ?_
    have hsp : s ≠ 1 - ρ := by simpa using hs.2
    have hsub : s - (1 - ρ) ≠ 0 := sub_ne_zero.mpr hsp
    have hne : s + ρ ≠ 1 := fun h => hsp (by rw [← h]; ring)
    change riemannZeta (s + ρ) * H s
      = (H s + zetaHol (s + ρ) * H s * (s - (1 - ρ))) / (s - (1 - ρ))
    rw [riemannZeta_eq_add_zetaHol hne, show (s + ρ) - 1 = s - (1 - ρ) from by ring]
    field_simp
  rw [hcongr, rectBI_cif_eq hφdiff hzw_re hzw_im hp_re hp_im, hφdef]
  simp

/-- **M3-1 — the DH pole term (unshifted, concrete).** For `χ ≠ 1`, `x > 0`, and a rectangle in
the right half-plane straddling `s = 1` (`0 < z.re < 1 < w.re`, `z.im < 0 < w.im`), the boundary
integral of the product-detector integrand `ζ(s)·L(s,χ)·x^{s+1}/(s(s+1))` extracts the
`L(1,χ)`-carrying residue:

`∮_{∂R} ζ(s)·L(s,χ)·x^{s+1}/(s(s+1)) ds = 2πi · L(1,χ)·x²/(1·2)`.

This is the exact competing MAIN TERM of the DH balance (the unshifted `ρ = 0` case; the shifted
`ρ`-case has pole `s = 1−ρ` and residue `L(1,χ)·x^{2−ρ}·G(1−ρ)/((1−ρ)(2−ρ))`). The `L(1,χ)` here
is the quantity the floor `dhDetector_floor` competes against — small `L(1,χ)` ⟹ repulsion. -/
theorem rectBI_zeta_LFunction_kernel {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {z w : ℂ} {x : ℝ} (hx : 0 < x) (hz_re0 : 0 < z.re)
    (hz_re : z.re < 1) (hw_re : 1 < w.re) (hz_im : z.im < 0) (hw_im : 0 < w.im) :
    rectBI z w (fun s => riemannZeta s *
        (DirichletCharacter.LFunction χ s * ((x : ℂ) ^ (s + 1) / (s * (s + 1)))))
      = 2 * ↑Real.pi * I *
        (DirichletCharacter.LFunction χ 1 * ((x : ℂ) ^ ((1 : ℂ) + 1) / (1 * (1 + 1)))) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hzw_re : z.re < w.re := lt_trans hz_re hw_re
  have hH : DifferentiableOn ℂ
      (fun s => DirichletCharacter.LFunction χ s * ((x : ℂ) ^ (s + 1) / (s * (s + 1))))
      (closedRect z w) := by
    intro s hs
    have hmem : s.re ∈ Set.Icc z.re w.re := by
      rw [← Set.uIcc_of_le hzw_re.le]; exact hs.1
    have hsre : 0 < s.re := lt_of_lt_of_le hz_re0 hmem.1
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
    have hs1 : s + 1 ≠ 0 := fun h => by
      have : (s + 1).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.one_re] at this; linarith
    refine ((DirichletCharacter.differentiable_LFunction hχ s).mul (DifferentiableAt.div ?_ ?_ ?_)
      ).differentiableWithinAt
    · exact (differentiableAt_id.add_const 1).const_cpow (Or.inl hxC)
    · exact differentiableAt_id.mul (differentiableAt_id.add_const 1)
    · exact mul_ne_zero hs0 hs1
  exact rectBI_zeta_mul hH hz_re hw_re hz_im hw_im

/-! ## M3-2 / M3-3 / M4 — the named obstruction map (PROSE, not `sorry`)

M3-1 (LANDED above) supplies the pole side of the DH balance: the residue theorems
`rectBI_zeta_mul` / `rectBI_zeta_shift_mul` and the concrete `L(1,χ)`-term
`rectBI_zeta_LFunction_kernel`. What remains for `dh_repulsion` (the target in
`DHRepulsion.lean`'s closing docstring), keyed to the landed suppliers:

### M3-3 — the shifted-line bound `J` (the bulk; NAMED)

On the vertical line `Re s = 1/2 − β`, bound `|J| = |∮_{line} F(s+ρ)·G(s+ρ)·x^s/(s(s+1)) ds|` via:
* `Growth.LFunction_growth` (`Re ≥ 1/2`, convexity-grade, constants free) for the two L-factors
  `L(1/2+it, χ)` and `L(1/2+it, χχ₁)` of `F`;
* `GrahamWeights.sum_abs_grahamTheta_rpow_le` (the σ-weighted `G`-sum bound);
* the landed kernel's `1/((s)(s+1))` DECAY — this `1/|s|²` is why the Riesz kernel was chosen
  (absolute convergence of the vertical integral; the finite-`N` case is `integrable_Fterm`,
  already landed and consumed by `dhDetector_mellin`);
* `StripConvergence.norm_LFunction_sub_partial_le_strip` for the DH-STRIP tails.
THE FIGHT (assembly): several hundred lines of uniform-in-`t` product-growth estimates
(Benli Lem 4.3, (5.7)–(5.17)). This is the genuine multi-session bulk; NOT attempted here.

### M3-2 — the rectangle close (NAMED)

Assemble `dhDetector_mellin` (the exact finite Mellin form on `Re s = c > 0`) with the residue
theorems above via `ContourShift.rectBI` on a tall rectangle `[1/2−β, c] × [−T, T]`. The
horizontal-edge integrals must vanish as `T → ∞` (uniform product growth of `F·G`). PRIMARY route:
the full `rectBI` shift (the shifted residue `rectBI_zeta_shift_mul` is ready). SANCTIONED FALLBACK
(predecessor's docstring): the vertical-only variant — write the detector directly as the
`Re s = 1 + 1/log x` line integral (no rectangle, no horizontal edges), trading the clean residue
for a direct estimate against the zero-damped detector. ROUTE NOT YET CHOSEN: M3-2 depends on M3-3
landing first (the horizontal-edge control IS item 3's fight); the fallback becomes attractive iff
that control proves intractable.

### M4 — the balance + inversion (NAMED; folds in once M3-2/M3-3 land)

From `|D_ρ| ≤ |residue| + |J|` and the reverse-triangle floor (`dhDetector_floor`), balancing at
`log x ≍ log(q(|γ|+2))` gives `L(1,χ₁) ≳ x^{−b(1−β)}/polylog`; then
`SiegelClose.LFunction_one_re_le_mvt_sharp` INVERTS to the target `1 − β₀` lower bound
(the reversed Jutila-(1.10) shape) — constants FREE.

### Honesty (HB-ENGINE, R4)

NO twin claim. `dh_repulsion` is one input to WP2, itself gated behind R4 (beyond-level-½ /
Kloosterman — the documented death rung).
-/

end Salt.SW

end
