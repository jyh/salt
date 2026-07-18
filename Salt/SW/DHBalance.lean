/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.DHContour
import Salt.SW.Growth
import Salt.SW.StripConvergence
import Salt.SW.SiegelClose
import Salt.SW.ZetaPartialFractions

/-!
# The Deuring–Heilbronn balance: M3-3 pointwise bound + M4 inversion (HB-ENGINE, DH-2b-iv)

Design: `docs/exploration/s3-hb3-design.md`, "DH-2b — THE PRODUCT-DETECTOR FREEZE".
Source: Benlİ–Goel–Twiss–Zaman, arXiv:2410.06082, §§4–5.

The predecessors landed:
* `DHRepulsion` (DH-2b-ii): the detector, the positivity floor (`dhDetector_floor`,
  `dhDetector_pos`), the finite Mellin representation (`dhDetector_mellin`), the
  Dirichlet-series identity (`dhLSeries_identity`).
* `DHContour` (DH-2b-iii): the additive ζ Laurent split (`zetaHol`), the residue payloads
  (`rectBI_zeta_mul`, `rectBI_zeta_shift_mul`, `rectBI_zeta_LFunction_kernel`).

This module (DH-2b-iv) supplies the **integrand-level** ingredients of the shifted-line
bound `J` (M3-3) and the **inversion** step (M4), plus a corrected obstruction map:

* **M3-3a — the Graham factor bound** (`norm_dhGpoly_le`): `‖G(z,s)‖ ≤ (z^{1−σ}(1+log z))²`
  on `0 < σ ≤ 1`, from `sum_abs_grahamTheta_rpow_le`. The clean, reusable `G`-side stone.
* **M3-3b — a clean ζ growth bound** (`norm_riemannZeta_le`): `‖ζ(s)‖ ≤ (…)/‖s−1‖` on
  `Re s > 0`, extracted from the corpus's `Zc_growth`. Reusable corpus-wide.
* **M3-3c — the pointwise integrand bound** (`norm_dhIntegrand_le`): the explicit product
  bound on `‖ζ·L·G·x^s/(s(s+1))‖` on the line `Re s = σ₀ ∈ [1/2, 1)`, packaging the three
  growth suppliers + the kernel decay. This is the analytic core of `J`, at the pointwise
  level.
* **M4 — the inversion** (`dh_repulsion_of_LFunction_one_lower`): given a lower bound on
  `(L(1,χ)).re` (the output of the DH balance), `LFunction_one_re_le_mvt_sharp` inverts it
  to the reversed-Jutila `1 − β₀` lower bound. The endgame, ready for the balance to feed it.

## The obstruction (a correction to the design's optimism)

The design predicted a "crude polynomial-in-t bound suffices since the kernel gives t⁻²".
With the corpus's ACTUAL suppliers this is FALSE: `Zc_growth` gives `‖ζ(σ₀+it)‖ = O(|t|)`
(linear, not convexity-grade), and `LFunction_growth` gives `‖L(σ₀+it,χ)‖ = O(|t|)`. Their
product is `O(|t|²)`, which the kernel's `1/‖s(s+1)‖ = O(|t|⁻²)` only cancels — leaving an
`O(1)` integrand, NOT integrable over ℝ. The sharp log-grade `zeta_log_bound`
(`O(log(|t|+2))`) holds only on the shrinking neighborhood `σ ≥ 1 − 1/log(|t|+2)`, so on a
fixed line `Re = σ₀ < 1` it covers only bounded `|t|`. Closing `J` as a genuine integral
bound therefore requires EITHER a subconvexity input (`‖L‖ ≲ |t|^{1/4}`, not in the corpus)
OR the finite-`N` truncation route (the detector's own finite Dirichlet polynomial IS
integrable — `integrable_Fterm` — at the cost of the `StripConvergence` truncation error).
See the closing docstring for the precise resume map.

## Honesty / death map (HB-ENGINE, R4 — NO twin claim)

NOT a proof of the Twin Prime Conjecture. Delivers competing-estimate substrate for the
conditional `InfinitelyManySiegelZeros → TwinPrimeConjecture`; the death rung is R4.
-/

open Complex

noncomputable section

namespace Salt.SW

/-! ## M3-3a — the Graham factor `G(z,s) = (Σ_{d≤z} θ_d d^{-s})²` and its norm bound

The Graham/Barban–Vehov Dirichlet polynomial (Benli's `G`) is the `t`-BOUNDED factor of the
DH integrand: its norm is controlled purely by `σ = Re s`, with NO `t`-growth. This is why
`G` never fights the kernel — the fight (below) is entirely in the `ζ·L` factor. -/

/-- The linear Graham Dirichlet polynomial `G₁(z,s) = Σ_{d=1}^{z} θ_d · d^{-s}` (the
"square root" of Benli's `G`). -/
noncomputable def dhGlin (z : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 z, (grahamTheta z d : ℂ) * (d : ℂ) ^ (-s)

/-- **Benli's Graham factor** `G(z,s) = (Σ_{d≤z} θ_d d^{-s})²`. -/
noncomputable def dhGpoly (z : ℕ) (s : ℂ) : ℂ := (dhGlin z s) ^ 2

/-- **M3-3a (linear form).** On `0 < σ ≤ 1`, `‖G₁(z,s)‖ ≤ z^{1−σ}(1 + log z)`. Termwise
`‖θ_d d^{-s}‖ = |θ_d|·d^{−σ} = |θ_d|/d^{σ}`, then the σ-weighted G-sum
`sum_abs_grahamTheta_rpow_le`. NO `t`-dependence: the bound is in `σ` alone. -/
lemma norm_dhGlin_le {z : ℕ} (hz : 2 ≤ z) {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) :
    ‖dhGlin z s‖ ≤ (z : ℝ) ^ (1 - s.re) * (1 + Real.log z) := by
  have hterm : ∀ d ∈ Finset.Icc 1 z,
      ‖(grahamTheta z d : ℂ) * (d : ℂ) ^ (-s)‖ = |grahamTheta z d| / (d : ℝ) ^ s.re := by
    intro d _
    rw [norm_mul, norm_natCast_cpow_neg hσ0, Complex.norm_real, Real.norm_eq_abs,
      Real.rpow_neg (Nat.cast_nonneg d), div_eq_mul_inv]
  rw [dhGlin]
  calc ‖∑ d ∈ Finset.Icc 1 z, (grahamTheta z d : ℂ) * (d : ℂ) ^ (-s)‖
      ≤ ∑ d ∈ Finset.Icc 1 z, ‖(grahamTheta z d : ℂ) * (d : ℂ) ^ (-s)‖ :=
        norm_sum_le _ _
    _ = ∑ d ∈ Finset.Icc 1 z, |grahamTheta z d| / (d : ℝ) ^ s.re :=
        Finset.sum_congr rfl hterm
    _ ≤ (z : ℝ) ^ (1 - s.re) * (1 + Real.log z) := sum_abs_grahamTheta_rpow_le hz hσ0 hσ1

/-- **M3-3a (the Graham factor bound).** On `0 < σ ≤ 1`, `‖G(z,s)‖ ≤ (z^{1−σ}(1+log z))²`.
The square of the linear bound; `t`-independent. This is the `G`-side of the DH integrand. -/
lemma norm_dhGpoly_le {z : ℕ} (hz : 2 ≤ z) {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) :
    ‖dhGpoly z s‖ ≤ ((z : ℝ) ^ (1 - s.re) * (1 + Real.log z)) ^ 2 := by
  rw [dhGpoly, norm_pow]
  gcongr
  exact norm_dhGlin_le hz hσ0 hσ1

/-! ## M3-3b — a clean ζ growth bound on `Re s > 0`

Extracted from the corpus's `Zc_growth` (`‖(s−1)ζ(s)‖ ≤ 1 + ‖s−1‖‖s‖(1+1/σ)`) by dividing
out `‖s−1‖`. This is the ONLY all-line ζ bound the corpus offers; it is LINEAR in `|t|`
(numerator `O(|t|²)` over `‖s−1‖ = O(|t|)`), the source of the M3-3 obstruction above. -/

/-- **M3-3b — the ζ growth bound.** For `Re s > 0` and `s ≠ 1`,
`‖ζ(s)‖ ≤ (1 + ‖s−1‖·‖s‖·(1 + 1/Re s)) / ‖s−1‖`. From `Zc_growth` via `ζ(s) = Zc(s)/(s−1)`.
Reusable corpus-wide; the `ζ`-side of the DH integrand. -/
lemma norm_riemannZeta_le {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ (1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re))) / ‖s - 1‖ := by
  have hsub : (0 : ℝ) < ‖s - 1‖ := by rw [norm_pos_iff]; exact sub_ne_zero.mpr hs1
  have hg : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := by
    have hz := Zc_growth hσ
    rwa [Zc_eq_of_ne hs1, norm_mul] at hz
  rw [le_div_iff₀ hsub]
  calc ‖riemannZeta s‖ * ‖s - 1‖ = ‖s - 1‖ * ‖riemannZeta s‖ := by ring
    _ ≤ 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := hg

/-! ## M3-3c — the pointwise integrand bound on the line `Re s = σ₀ ∈ [1/2, 1)`

The unshifted DH integrand `ζ(s)·L(s,χ)·G(z,s)·x^s/(s(s+1))` — the `ρ = 0` product frame the
shift builds on (matching `rectBI_zeta_LFunction_kernel`, with the Graham factor restored).
Its norm factors into the four suppliers: `ζ` (`norm_riemannZeta_le`), `L`
(`LFunction_growth`), `G` (`norm_dhGpoly_le`), and the kernel decay `x^σ/(‖s‖‖s+1‖)`. This is
the analytic core of the shifted-line bound `J`, at the pointwise level.

**The obstruction, made concrete.** In this bound the `ζ`-factor is `O(‖s‖·(1+1/σ)) = O(|t|)`
and the `L`-factor is `O(1+‖s‖) = O(|t|)`; their product is `O(|t|²)`, and the kernel decay is
`O(|t|⁻²)`. So `‖dhIntegrand(σ₀+it)‖ = O(1)` — bounded but NOT integrable over `t ∈ ℝ`. The
integral form of `J` (`∫_ℝ ‖dhIntegrand‖ dt < ∞`) is therefore NOT deducible from this bound;
it needs subconvexity (each `L`-factor `≲ |t|^{1/4}`) or the finite-`N` truncation. -/

/-- The unshifted DH product-detector integrand `ζ(s)·L(s,χ)·G(z,s)·x^s/(s(s+1))`. -/
noncomputable def dhIntegrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (z : ℕ) (x : ℝ) (s : ℂ) : ℂ :=
  riemannZeta s * DirichletCharacter.LFunction χ s * dhGpoly z s *
    ((x : ℂ) ^ s / (s * (s + 1)))

/-- **M3-3c — the pointwise integrand bound.** On the line `Re s = σ₀ ∈ [1/2, 1)` (for a
primitive `χ` mod `q ≥ 2`, `z ≥ 2`, `x > 0`), the DH integrand's norm is bounded by the
explicit product of the four suppliers. Fully verifiable; the analytic core of `J`.

The bound is `O(1)` in `t` (see the obstruction note): the linear `ζ·L` numerator only
cancels the kernel's quadratic decay, so the vertical integral over ℝ does NOT converge from
this alone — the named next obstruction. -/
theorem norm_dhIntegrand_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {z : ℕ} (hz : 2 ≤ z) {x : ℝ} (hx : 0 < x)
    {s : ℂ} (hσlo : (1 : ℝ) / 2 ≤ s.re) (hσhi : s.re < 1) :
    ‖dhIntegrand χ z x s‖
      ≤ ((1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re))) / ‖s - 1‖)
        * (3 * (1 + ‖s‖) * Real.sqrt q * (1 + Real.log q))
        * (((z : ℝ) ^ (1 - s.re) * (1 + Real.log z)) ^ 2)
        * (x ^ s.re / (‖s‖ * ‖s + 1‖)) := by
  have hσ0 : 0 < s.re := by linarith
  have hσ1 : s.re ≤ 1 := le_of_lt hσhi
  have hs1 : s ≠ 1 := by rintro rfl; rw [Complex.one_re] at hσhi; exact lt_irrefl 1 hσhi
  -- Factor the norm into the four factors.
  have key : ‖dhIntegrand χ z x s‖
      = ‖riemannZeta s‖ * ‖DirichletCharacter.LFunction χ s‖ * ‖dhGpoly z s‖
        * (x ^ s.re / (‖s‖ * ‖s + 1‖)) := by
    rw [dhIntegrand, norm_mul, norm_mul, norm_mul, norm_div, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
  -- The four supplier bounds and the nonnegativity facts.
  have hZ := norm_riemannZeta_le hσ0 hs1
  have hL := LFunction_growth χ hχ hq hσlo (by linarith)
  have hG := norm_dhGpoly_le hz hσ0 hσ1
  have hKnn : 0 ≤ x ^ s.re / (‖s‖ * ‖s + 1‖) := by positivity
  have hZBnn : 0 ≤ (1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re))) / ‖s - 1‖ :=
    le_trans (norm_nonneg _) hZ
  have hLBnn : 0 ≤ 3 * (1 + ‖s‖) * Real.sqrt q * (1 + Real.log q) :=
    le_trans (norm_nonneg _) hL
  rw [key]
  refine mul_le_mul_of_nonneg_right ?_ hKnn
  exact mul_le_mul (mul_le_mul hZ hL (norm_nonneg _) hZBnn) hG (norm_nonneg _)
    (mul_nonneg hZBnn hLBnn)

/-! ## M4 — the inversion `(L(1,χ)).re ≥ Λ  ⟹  1 − β₀ ≥ Λ / (25e(1+log q)²)`

The last step of the DH balance. The competing estimates (floor `≤` main `+` error) produce a
LOWER bound `Λ ≤ (L(1,χ)).re`; the sharp Siegel MVT `LFunction_one_re_le_mvt_sharp` gives the
matching UPPER bound `(L(1,χ)).re ≤ (1−β₀)·25e(1+log q)²`. Chaining them inverts to the
reversed-Jutila `1 − β₀` lower bound. This lemma is UNCONDITIONAL given `Λ`; the balance's job
is to produce `Λ ≍ x^{−b(1−ρ.re)}/polylog` (the residual, gated behind the `J` integral). -/

/-- **M4 — the inversion.** For a primitive `χ` mod `q ≥ 2` with a real zero `β ∈
[1 − 1/(4(1+log q)), 1)`, any lower bound `Λ ≤ (L(1,χ)).re` inverts to
`1 − β ≥ Λ / (25e(1+log q)²)`. The Siegel-MVT endgame of the DH balance, ready for the
`L(1,χ)` lower bound the (residual) `J`-integral would supply. -/
theorem dh_repulsion_of_LFunction_one_lower {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {β : ℝ}
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hβlo : 1 - 1 / (4 * (1 + Real.log q)) ≤ β) (hβhi : β < 1)
    {Λ : ℝ} (hΛ : Λ ≤ (DirichletCharacter.LFunction χ 1).re) :
    Λ / (25 * Real.exp 1 * (1 + Real.log q) ^ 2) ≤ 1 - β := by
  have hlog : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have h1 : 0 < 1 + Real.log q := by linarith
  have hK : 0 < 25 * Real.exp 1 * (1 + Real.log q) ^ 2 :=
    mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) (pow_pos h1 2)
  have hMVT := LFunction_one_re_le_mvt_sharp χ hχ hq hzero hβlo hβhi
  rw [div_le_iff₀ hK]
  exact le_trans hΛ hMVT

/-! ## The resume map (DH-2b-iv → next; PROSE, not `sorry`)

LANDED here (all sorry-free, axioms `⊆ [propext, Classical.choice, Quot.sound]`):
* `norm_dhGpoly_le` — the Graham factor bound (M3-3a), `t`-independent.
* `norm_riemannZeta_le` — a clean all-line ζ growth bound (M3-3b), corpus-reusable.
* `norm_dhIntegrand_le` — the pointwise DH integrand bound (M3-3c): the analytic core of `J`.
* `dh_repulsion_of_LFunction_one_lower` — the Siegel-MVT inversion (M4): the endgame, ready.

### The single remaining obstruction (corrected from the design)

`norm_dhIntegrand_le` is `O(1)` in `t`, NOT `o(t⁻¹)`: the corpus's `ζ` and `L` bounds are
each LINEAR in `|t|` (`Zc_growth`, `LFunction_growth`), so their product is `O(|t|²)` and the
kernel's `O(|t|⁻²)` only cancels it. Hence:

* **`J` as an integral over ℝ does NOT converge** from the landed bounds. Closing it needs
  EITHER (a) a subconvexity input `‖L(σ₀+it,χ)‖ ≲ |t|^{1/4+ε}` (or even any `|t|^{1−δ}`) —
  NOT in the corpus, a genuine analytic-number-theory build; OR (b) the finite-`N` truncation
  route: bound the detector via its own finite Dirichlet polynomial (`dhDetector_mellin`,
  `integrable_Fterm` — the finite integrand IS integrable), paying the `StripConvergence`
  truncation error `norm_LFunction_sub_partial_le_strip` and optimizing `N ≍ x`.
* **M3-2 (the rectangle close)** has the SAME obstruction: the horizontal edges of `rectBI`
  do NOT vanish as `T → ∞` under the `O(1)` integrand (edge integrand `= O(x^c)`, not `o(1)`).
  The residue side is fully ready (`rectBI_zeta_shift_mul`, `rectBI_zeta_LFunction_kernel`);
  only the edge-vanishing needs the subconvexity/truncation input above.
* **M4** is DONE modulo the `L(1,χ)` lower bound `Λ` that the closed `J`-balance produces:
  feed `dh_repulsion_of_LFunction_one_lower` with `Λ ≍ x^{−b(1−ρ.re)}/polylog` and tune
  `x = (q(|ρ.im|+2))^{b'}` to reach the `dh_repulsion` target shape.

RECOMMENDED next attempt: route (b) (finite-`N` truncation) — it stays inside the corpus (no
new subconvexity), and the truncation error is already the landed
`norm_LFunction_sub_partial_le_strip`. The trade is a longer `N`-optimization bookkeeping in
place of the (unbuilt) subconvexity. This is the honest multi-session bulk that remains.

### Honesty (HB-ENGINE, R4)

NO twin claim. `dh_repulsion` is one input to WP2, itself gated behind R4 (beyond-level-½ /
Kloosterman — the documented death rung). -/

end Salt.SW

end
