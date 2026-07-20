/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Kernel

/-!
# S8 MR-CORE, node A3a-R1 — the sharp continuous Perron representation (LADDER)

Source pin: **MR arXiv v4** (`docs/sources/1501.04585v4.pdf`), §7 "Parseval bound",
pp. 21–23; cross-checked against Montgomery–Vaughan (`docs/sources/montgomery3.txt`,
§23 pp. 31–32).

## The dissolution verdict (A3a-R1, the `#255` scoper check)

The raw target (MR v4 p. 21, bottom) is Perron's formula
`Sⱼ(x) = (1/2πi) ∫_{1−i∞}^{1+i∞} A(s)·((x+hⱼ)ˢ−xˢ)/s ds`, `A(s) = ∑_{X≤m≤4X} aₘ/mˢ`.
The kernel `((x+h)ˢ−xˢ)/s` decays **only like `1/|t|`** (MVT numerator `≤ ‖s‖·xᶜ·h`,
over `s`), so the single vertical integral is only *conditionally* convergent —
mathlib-absent, correctly priced D.

**But MR never consume the raw representation as an absolutely-convergent object.**
Their §7 proof (pp. 22–23) immediately splits at `T₀ = (log X)^{1/15}` into
`Uⱼ` (`|t| ≤ T₀`) and `Vⱼ` (`|t| > T₀`):

* `Uⱼ` uses only the **truncated** integral `∫_{1−iT₀}^{1+iT₀}` (a *finite* interval,
  absolutely convergent) — a Taylor expansion of `((x+hⱼ)ˢ−xˢ)/s = xˢ(hⱼ/x + O(…))`
  gives the `1/(log X)^{2/15}` main term (this is the residual `A3a-R2`).
* `Vⱼ` appears **only inside the mean square** `(1/X)∫_X^{2X}(|Vⱼ(x)|/hⱼ)² dx`.  There
  MR remove the `1/|t|` obstruction NOT by smoothing the kernel but by *averaging over
  `x`* + Parseval (MR p. 23: smooth cut-off `g(x/X)`, expand the square, `∫ … dx` gives
  the `|t₁−t₂|^{−2}` gain).  Montgomery–Vaughan state the same principle **verbatim**
  (p. 32): *"the kernel in Perron's formula decays only like an inverse first power.
  This could be overcome by smoothing, but … we avoided that problem by averaging over
  x, which allows us to appeal to Plancherel's identity."*

**CATCH (executor-refutes-brief-hypothesis).**  The dispatch brief conjectured that the
Saffari–Vaughan `w`-average of `((x+w)ˢ−xˢ)/s` over `w ∈ [h,3h]` has the hat-kernel's
`1/t²` decay class, so the averaged representation would be absolutely convergent and
provable by the `hat_contour_rep` route.  This is **false**: the landed
`sv_average_kernel` shows the `w`-average is *tautological* — the smooth `(x+w)ˢ` parts
cancel (`F − G = const`), recovering the sharp `1/|t|` kernel exactly.  The decay that
saves MR is the `x`-average (Plancherel), a different mechanism.  So the averaged
representation is **not** absolutely convergent, and the `hat_contour_rep` route does
**not** apply to it.  The D does not fully dissolve — but it relocates: the mean-square
`Vⱼ` core is the landed `lpoly_mean_sq_bound`/`dirichlet_poly_l2_mvt_final`, and the
genuinely irreducible piece is the **truncated Perron with error** for `Uⱼ` (below).

## What lands here (the buildable rungs)

* `cpow_ratio_seg_bound` — the segment/MVT bound `‖(1+u)ˢ − 1‖ ≤ ‖s‖·(1+u)ᶜ·u`.
* `sv_smooth_kernel_bound` — the `Vⱼ` Parseval kernel bound
  `‖((1+u)ˢ − 1)/s‖ ≤ (1+u)ᶜ·min(u, 2/‖s‖)`.  This is exactly MR p. 23's
  `min{hⱼ/X, 1/|t|}` (with `u ≪ hⱼ/X`, `(1+u)ᶜ ≈ 1`): the kernel that carries the `Vⱼ`
  tail into the Parseval step.  `s` abbreviates `(c:ℂ)+(t:ℂ)·I` (the `SW.Kernel`
  convention, so the landed identities unify).

## What resists (the resistance map — see the wave NOTES)

The **truncated Perron with explicit error** — per-term
`(1/2πi)∫_{c−iT}^{c+iT} yˢ/s ds = 𝟙(y>1) + O(yᶜ/(T·|log y|))` (Montgomery–Vaughan
Theorem 5.1 / Davenport §17) — is the irreducible D-core for `Uⱼ`.  Its kernel `yˢ/s`
is not absolutely integrable (unlike the landed `SW.kernel_identity`, which uses the
*smoothed* `yˢ/(s(s+1))` precisely to stay absolutely convergent); mathlib has no
discontinuous-Perron primitive.  Building it needs the full contour + arc-error
apparatus (the same class as `SW.ContourShift`).
-/

open MeasureTheory Complex Set
open scoped BigOperators

noncomputable section
namespace Salt.MR

/-! ## The `Vⱼ` Saffari–Vaughan smoothed kernel `((1+u)ˢ − 1)/s`. -/

/-- **Segment (MVT) bound on the smoothed numerator** (`A3a-R1` rung).  For a vertical
line `Re s = c > 0` and `u ≥ 0`, `‖(1+u)ˢ − 1‖ ≤ ‖s‖·(1+u)ᶜ·u`.  This is the MR p. 22
kernel `((1+u)ˢ−1)/s` numerator, bounded exactly as `cpow_seg_bound` bounds
`(X+h)^{s+1}−X^{s+1}`: the mean-value theorem on `y ↦ yˢ` over `[1, 1+u]`, with the
derivative `s·y^{s−1}` sup-bounded by `‖s‖·(1+u)ᶜ`. -/
theorem cpow_ratio_seg_bound {c : ℝ} (hc : 0 < c) (t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ‖((1 + u : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) - 1‖
      ≤ ‖(c : ℂ) + (t : ℂ) * I‖ * (1 + u) ^ c * u := by
  set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs
  have hsne : s ≠ 0 := by rw [hs]; exact Salt.SW.s_ne_zero hc t
  have hre : s.re = c := by rw [hs]; simp
  have hderiv : ∀ y ∈ Icc (1 : ℝ) (1 + u),
      HasDerivWithinAt (fun z : ℝ => (z : ℂ) ^ s) (s * (y : ℂ) ^ (s - 1))
        (Icc (1 : ℝ) (1 + u)) y := by
    intro y hy
    have hy0 : y ≠ 0 := by rw [mem_Icc] at hy; nlinarith [hy.1]
    exact (hasDerivAt_ofReal_cpow_const hy0 hsne).hasDerivWithinAt
  have hbound : ∀ y ∈ Icc (1 : ℝ) (1 + u),
      ‖s * (y : ℂ) ^ (s - 1)‖ ≤ ‖s‖ * (1 + u) ^ c := by
    intro y hy
    rw [mem_Icc] at hy
    have hy0 : 0 < y := by linarith [hy.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
      show (s - 1).re = c - 1 by rw [Complex.sub_re, hre]; simp]
    gcongr
    -- `y^{c-1} ≤ (1+u)^c` for `1 ≤ y ≤ 1+u`, `c > 0`
    calc y ^ (c - 1)
        ≤ y ^ c := Real.rpow_le_rpow_of_exponent_le (by linarith [hy.1]) (by linarith)
      _ ≤ (1 + u) ^ c := Real.rpow_le_rpow (by linarith [hy.1]) hy.2 hc.le
  have hmvt := (convex_Icc (1 : ℝ) (1 + u)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
  rw [Complex.ofReal_one, Complex.one_cpow] at hmvt
  calc ‖((1 + u : ℝ) : ℂ) ^ s - 1‖
      ≤ ‖s‖ * (1 + u) ^ c * ‖(1 + u) - (1 : ℝ)‖ := hmvt
    _ = ‖s‖ * (1 + u) ^ c * u := by
        rw [show (1 + u) - (1 : ℝ) = u by ring, Real.norm_of_nonneg hu]

/-- **The `Vⱼ` Parseval kernel bound** (`A3a-R1` rung).  On `Re s = c > 0`, `u ≥ 0`,
`‖((1+u)ˢ − 1)/s‖ ≤ (1+u)ᶜ·min(u, 2/‖s‖)`.  This is MR p. 23's `min{hⱼ/X, 1/|t|}`
(with `u ≪ hⱼ/X` and `(1+u)ᶜ ≈ 1`): the `u`-branch from the MVT numerator
(`cpow_ratio_seg_bound`), the `2/‖s‖`-branch from the trivial `‖(1+u)ˢ − 1‖ ≤ 2(1+u)ᶜ`.
Together they give the second-order-in-`min` control the mean-square Parseval step needs. -/
theorem sv_smooth_kernel_bound {c : ℝ} (hc : 0 < c) (t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ‖(((1 + u : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) - 1)
        / ((c : ℂ) + (t : ℂ) * I)‖
      ≤ (1 + u) ^ c * min u (2 / ‖(c : ℂ) + (t : ℂ) * I‖) := by
  set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr (by rw [hs]; exact Salt.SW.s_ne_zero hc t)
  have h1u : (1 : ℝ) ≤ 1 + u := by linarith
  have hpow1 : (1 : ℝ) ≤ (1 + u) ^ c := Real.one_le_rpow h1u hc.le
  have hpow0 : (0 : ℝ) ≤ (1 + u) ^ c := by positivity
  rw [norm_div]
  -- the `u`-branch (MVT numerator / ‖s‖)
  have hbu : ‖((1 + u : ℝ) : ℂ) ^ s - 1‖ / ‖s‖ ≤ (1 + u) ^ c * u := by
    rw [div_le_iff₀ hsn]
    refine (cpow_ratio_seg_bound hc t hu).trans_eq ?_
    rw [← hs]; ring
  -- the `2/‖s‖`-branch (trivial triangle bound / ‖s‖)
  have hbt : ‖((1 + u : ℝ) : ℂ) ^ s - 1‖ / ‖s‖ ≤ (1 + u) ^ c * (2 / ‖s‖) := by
    rw [div_le_iff₀ hsn]
    have htri : ‖((1 + u : ℝ) : ℂ) ^ s - 1‖ ≤ 2 * (1 + u) ^ c := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < 1 + u),
        show s.re = c by rw [hs]; simp, norm_one]
      linarith
    refine htri.trans_eq ?_
    rw [mul_assoc, div_mul_cancel₀ (2 : ℝ) hsn.ne']
    ring
  exact (le_min hbu hbt).trans_eq (mul_min_of_nonneg _ _ hpow0).symm

/-- **The "take out `xˢ`" factorization** (`A3a-R1`/R4 bridge; MR v4 p. 22).  For
`x > 0`, `x + h > 0` and any `s`, the sharp Perron kernel factors through the smoothed
kernel of `sv_smooth_kernel_bound` at `u = h/x`:
`((x+h)ˢ − xˢ)/s = xˢ·((1 + h/x)ˢ − 1)/s`.  Composing with `sv_smooth_kernel_bound`
(on `Re s = c > 0`, `h ≥ 0`) gives the sharp integrand modulus
`≤ xᶜ·(1+h/x)ᶜ·min(h/x, 2/‖s‖)` — MR p. 23's `min{hⱼ/X, 1/|t|}`, the `Uⱼ`/`Vⱼ`
consumer form for `A3a-R2`. -/
lemma sharp_kernel_factor {x h : ℝ} (hx : 0 < x) (hxh : 0 < x + h) (s : ℂ) :
    (((x + h : ℝ) : ℂ) ^ s - ((x : ℝ) : ℂ) ^ s) / s
      = ((x : ℝ) : ℂ) ^ s * ((((1 + h / x : ℝ) : ℂ) ^ s - 1) / s) := by
  have h1x : (0 : ℝ) < 1 + h / x := by
    rw [show (1 : ℝ) + h / x = (x + h) / x by field_simp]; exact div_pos hxh hx
  have hfac : ((x + h : ℝ) : ℂ) ^ s = ((x : ℝ) : ℂ) ^ s * ((1 + h / x : ℝ) : ℂ) ^ s := by
    rw [show (x + h : ℝ) = x * (1 + h / x) by field_simp, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hx.le h1x.le]
  rw [hfac]; ring

end Salt.MR
