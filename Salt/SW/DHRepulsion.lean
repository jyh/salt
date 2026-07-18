/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.DHDetector
import Salt.SW.GrahamWeights
import Salt.SW.Kernel

/-!
# The Deuring–Heilbronn competing-estimates assembly (HB-ENGINE, WP2, node DH-2b-ii)

Design: `docs/exploration/s3-hb3-design.md`, "DH-2b — THE PRODUCT-DETECTOR FREEZE".
Source: Benlİ–Goel–Twiss–Zaman, *Explicit Deuring–Heilbronn phenomenon for Dirichlet
L-functions* (arXiv:2410.06082), §§4–5. This module assembles the mollified
soft-Perron detector whose two competing estimates (a positivity floor vs. a contour
upper bound) yield the reversed Jutila-(1.10) zero-repulsion shape.

## The detector (Benli §§4–5, our `ζ·L(χ₁)` collapse of the product `F(s,χ)`)

For the diagonal HB need both relevant characters give the SAME product:
`F(s,χ₀) = ζ_q(s)·L(s,χ₁) = F(s,χ₁)`, whose coefficients on coprime `n` are exactly
the landed `dhA = 1∗χ_ℝ` (DH-1). The mollified detector is

  `D(x,N) = Σ_{n≤N} a(n)·(Σ_{d∣n} θ_d)²·(1 - n/x)₊`,   `a = dhA χ`,

with the landed Graham/Barban–Vehov weights `θ_d = grahamTheta z d` and the landed
smoothed Perron/Riesz kernel `(1-·)₊ = Re ∘ kern` (`Salt.SW.Kernel`).

## Milestones (the Zeno ladder, design §"THE PRODUCT-DETECTOR FREEZE")

* **M1 — the detector identity layer.** The Dirichlet-series form of the coefficient
  `a(n)`, `Σ a(n) n^{-s} = ζ(s)·L(s,χ)` on `Re s > 1` (`dhLSeries_identity`, closing
  DH-1's documented `dhLSeries_target` seam), and the Mellin representation of the
  mollified partial-sum via the landed kernel stack (`Salt.SW.Kernel`).
* **M2 — the floor** (`dhDetector_floor`, `dhDetector_pos`): `D(x,N) ≥ (1 - 1/x)₊`,
  from `grahamTheta_floor` (the `n = 1` weight square is `1`) + `dhA_nonneg` (the
  `1∗χ` positivity) + kernel nonnegativity. All terms are `≥ 0`; the `n = 1` term is
  `a(1)·θ₁²·(1-1/x)₊ = (1-1/x)₊`.
* **M3 — the upper contour** (NAMED OBSTRUCTION, see the closing docstring): the
  `rectBI`/`kernel_residue` shift of `F(s+ρ)G(s+ρ)`, the pole at `s = 1−ρ`
  (residue `≍ L(1,χ₁)·x^{1−β}`), the `s = 0` vanishing `F(ρ)G(ρ) = 0`, the
  shifted-line growth error (`LFunction_growth` + G-sums + `DH-STRIP` tails), the
  near-1 zero enumeration (`LFunction_zero_count_near_one`).
* **M4 — the balance + inversion** (NAMED): floor `≤` |pole| + |errors| forces
  `L(1,χ) ≳ x^{−b(1−β)}/polylog`; `LFunction_one_re_le_mvt_sharp` converts to the
  gap `1−β₀`; the target is `dh_repulsion` (the reversed Jutila-(1.10) shape).

## Honesty / death map (HB-ENGINE, R4 — NO twin claim)

This is NOT a proof of the Twin Prime Conjecture. The campaign target is the
conditional `InfinitelyManySiegelZeros → TwinPrimeConjecture` (the landed
`HeathBrownStatement` shape). This node delivers the competing-estimate substrate;
the predicted death rung is R4 (beyond-level-½ / Kloosterman error control).
-/

open Finset MeasureTheory Complex

noncomputable section

namespace Salt.SW

variable {q : ℕ}

/-! ## The real detector kernel `(1-·)₊` (the real part of the landed `kern`) -/

/-- The real smoothing kernel `(1 - t)₊ = max 0 (1 - t)` (equal to `(kern t).re`).
Nonnegative everywhere; positive for `t < 1`; the mollifier the detector rides on. -/
def dhKernR (t : ℝ) : ℝ := max 0 (1 - t)

@[simp] lemma dhKernR_nonneg (t : ℝ) : 0 ≤ dhKernR t := le_max_left _ _

lemma dhKernR_eq {t : ℝ} (ht : t ≤ 1) : dhKernR t = 1 - t := max_eq_right (by linarith)

lemma dhKernR_pos {t : ℝ} (ht : t < 1) : 0 < dhKernR t := by
  rw [dhKernR_eq ht.le]; linarith

/-- The real kernel is the real part of the landed complex kernel `kern`. -/
lemma dhKernR_eq_re_kern (t : ℝ) : dhKernR t = (kern t).re := by
  simp [dhKernR, kern]

/-! ## The Graham weight square `(Σ_{d∣n} θ_d)²` (the sieve positivity) -/

/-- The squared Graham/Barban–Vehov weight `w_z(n) = (Σ_{d∣n} θ_d)²` — the sieve
positivity of the detector: a square, hence `≥ 0`, and `= 1` at `n = 1` (`θ₁ = 1`). -/
noncomputable def dhWeightSq (z n : ℕ) : ℝ := (∑ d ∈ n.divisors, grahamTheta z d) ^ 2

@[simp] lemma dhWeightSq_nonneg (z n : ℕ) : 0 ≤ dhWeightSq z n := sq_nonneg _

lemma dhWeightSq_one {z : ℕ} (hz : 2 ≤ z) : dhWeightSq z 1 = 1 :=
  grahamTheta_floor hz

/-! ## The mollified detector `D(x,N)` and M2 — the positivity floor -/

/-- **The mollified soft-Perron detector** `D(x,N) = Σ_{n≤N} a(n)·w_z(n)·(1 - n/x)₊`
(Benli §§4–5). `a = dhA χ` (the `1∗χ_ℝ` divisor sum), `w_z = dhWeightSq z` (the Graham
square), and `(1-·)₊ = dhKernR` (the landed Riesz kernel's real part). -/
noncomputable def dhDetector (χ : DirichletCharacter ℂ q) (z : ℕ) (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, dhA χ n * dhWeightSq z n * dhKernR ((n : ℝ) / x)

/-- Every summand of the detector is nonnegative (for real `χ`): `a(n) ≥ 0` (the `1∗χ`
positivity floor), `w_z(n) ≥ 0` (a square), `(1-n/x)₊ ≥ 0`. -/
lemma dhDetector_term_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ) (x : ℝ)
    {n : ℕ} (hn : 1 ≤ n) : 0 ≤ dhA χ n * dhWeightSq z n * dhKernR ((n : ℝ) / x) :=
  mul_nonneg (mul_nonneg (dhA_nonneg χ hsq (by omega)) (dhWeightSq_nonneg z n))
    (dhKernR_nonneg _)

/-- **M2 — the positivity floor.** The detector dominates its `n = 1` term, which is
`a(1)·w_z(1)·(1 - 1/x)₊ = 1·1·(1 - 1/x)₊`. All other terms are nonnegative
(`dhDetector_term_nonneg`). This is the competing LOWER estimate of the DH balance. -/
lemma dhDetector_floor (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (x : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    dhKernR (1 / x) ≤ dhDetector χ z x N := by
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩
  have hterm : dhA χ 1 * dhWeightSq z 1 * dhKernR (((1 : ℕ) : ℝ) / x) = dhKernR (1 / x) := by
    rw [dhA_one, dhWeightSq_one hz, Nat.cast_one]; ring
  calc dhKernR (1 / x)
      = dhA χ 1 * dhWeightSq z 1 * dhKernR (((1 : ℕ) : ℝ) / x) := hterm.symm
    _ ≤ dhDetector χ z x N :=
        Finset.single_le_sum
          (fun n hn => dhDetector_term_nonneg χ hsq z x (Finset.mem_Icc.mp hn).1) h1mem

/-- **M2 (positive form).** For `x > 1` and `N ≥ 1`, the detector is strictly positive:
the `n = 1` term `(1 - 1/x)₊ = 1 - 1/x > 0` already forces it. -/
lemma dhDetector_pos (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    {x : ℝ} (hx : 1 < x) {N : ℕ} (hN : 1 ≤ N) :
    0 < dhDetector χ z x N := by
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hlt : 1 / x < 1 := (div_lt_one hx0).mpr hx
  exact lt_of_lt_of_le (dhKernR_pos hlt) (dhDetector_floor χ hsq hz x hN)

/-! ## M1a — the Mellin representation of the mollified detector (finite, exact)

The mollified detector equals a single vertical integral of its **finite Dirichlet
polynomial** against the landed smoothed-Perron kernel `x^s/(s(s+1))`. No summability
side-condition is needed: `kernel_identity` represents each term `(1 - n/x)₊`, and a
FINITE sum commutes with the integral (each summand is `integrable_Fterm`). This is the
`c > 0` interface the M3 contour shift consumes — the Dirichlet polynomial
`Σ_{n≤N} c(n)(x/n)^s` is Benli's `F(s+ρ)G(s+ρ)` truncation on the `Re s = c` line. -/

/-- The detector coefficient `c(n) = a(n)·w_z(n)` (the `1∗χ_ℝ` value times the Graham
square). Its Dirichlet series is Benli's `F(s)G(s)` (the diagonal collapse). -/
noncomputable def dhCoeff (χ : DirichletCharacter ℂ q) (z n : ℕ) : ℝ :=
  dhA χ n * dhWeightSq z n

lemma dhDetector_eq_coeff (χ : DirichletCharacter ℂ q) (z : ℕ) (x : ℝ) (N : ℕ) :
    dhDetector χ z x N
      = ∑ n ∈ Finset.Icc 1 N, dhCoeff χ z n * dhKernR ((n : ℝ) / x) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [dhCoeff, mul_assoc]

/-- **Per-term kernel representation.** For `x > 0`, `c > 0`, `n ≥ 1`, the real weight
`(1 - n/x)₊` is the vertical integral of `(x/n)^{c+ti}/((c+ti)(c+ti+1))`. Both the
`n ≤ x` branch (`1 - n/x`) and the `n > x` branch (`0`) are covered by
`kernel_identity` at `y = x/n`. -/
lemma dhKernR_eq_kernel_integral {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 < c) {n : ℕ}
    (hn : 1 ≤ n) :
    ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)
      = (1 / (2 * Real.pi)) • ∫ t : ℝ,
          ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
            (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hy : (0 : ℝ) < x / n := div_pos hx hn0
  rw [kernel_identity hy hc]
  by_cases h : (1 : ℝ) ≤ x / n
  · rw [if_pos h]
    have hnx : (n : ℝ) / x ≤ 1 := by
      rw [div_le_one hx]; rw [le_div_iff₀ hn0, one_mul] at h; exact h
    rw [dhKernR_eq hnx]
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    push_cast
    field_simp
  · rw [if_neg h]
    rw [not_le] at h
    have hxn : x < (n : ℝ) := (div_lt_one hn0).mp h
    have hle : (1 : ℝ) - (n : ℝ) / x ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hx, one_mul]; exact hxn.le
    rw [dhKernR, max_eq_left hle]
    simp

/-- **M1a — the finite Mellin representation.** For `x > 0` and any vertical line
`Re s = c > 0`, the mollified detector equals the single vertical integral of its finite
Dirichlet polynomial `Σ_{n≤N} c(n)(x/n)^{c+ti}` against the smoothed Perron kernel
`1/((c+ti)(c+ti+1))`. Exact and summability-free (finite `Σ↔∫` swap via
`integrable_Fterm`). This is the M1 Mellin seam the M3 contour shift consumes. -/
theorem dhDetector_mellin (χ : DirichletCharacter ℂ q) (z : ℕ) {x : ℝ} (hx : 0 < x)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ((dhDetector χ z x N : ℝ) : ℂ)
      = (1 / (2 * Real.pi)) • ∫ t : ℝ,
          (∑ n ∈ Finset.Icc 1 N,
              (dhCoeff χ z n : ℂ) * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) /
            (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
  -- Step 1: the detector as a finite sum of per-term kernel integrals.
  have hstep : ((dhDetector χ z x N : ℝ) : ℂ)
      = ∑ n ∈ Finset.Icc 1 N, (1 / (2 * Real.pi)) • ∫ t : ℝ,
          (dhCoeff χ z n : ℂ) * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
            (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
    rw [dhDetector_eq_coeff]
    push_cast
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [dhKernR_eq_kernel_integral hx hc hn1, mul_smul_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only; push_cast; ring
  rw [hstep, ← Finset.smul_sum]
  congr 1
  refine (integral_finsetSum (Finset.Icc 1 N)
    (fun n _ => integrable_Fterm (dhCoeff χ z n : ℂ)
      (div_nonneg hx.le (Nat.cast_nonneg n)) hc)).symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [Finset.sum_div]

/-! ## M1b — the Dirichlet-series identity `Σ a(n) n^{-s} = ζ(s)·L(s,χ)`

This closes the seam DH-1 left documented (`dhLSeries_target`, `DHDetector.lean:362`).
The coefficient `a = dhA χ = 1∗χ_ℝ` is the Dirichlet convolution of the constant `1`
(whose L-series is `ζ`) with the real character `χ_ℝ`; for a real character (`χ² = 1`)
the values `χ(n) ∈ {0,1,−1}` are their own real parts, so `↑(χ_ℝ n) = χ(n)` and the
convolution is `1 ∗ χ`. -/

/-- **The quadratic reality bridge.** For real `χ` (`χ² = 1`) the value `χ(n)` lies in
`{0,1,−1} ⊂ ℝ`, hence equals its own real part: `((χ_ℝ n : ℝ) : ℂ) = χ(n)`. -/
lemma chiRe_ofReal (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    ((chiRe χ n : ℝ) : ℂ) = χ (n : ZMod q) := by
  have hQ : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq
  unfold chiRe
  rcases hQ (n : ZMod q) with h | h | h <;> rw [h] <;> simp

open scoped LSeries.notation in
/-- **M1b — the detector Dirichlet-series identity** (DH-1's `dhLSeries_target`, landed).
For a real primitive-or-not character `χ` (`χ² = 1`) and `1 < Re s`,
`Σ_n a(n) n^{-s} = ζ(s)·L(s,χ)`, where `a = dhA χ = 1∗χ_ℝ`. Route: the coefficient is
the Dirichlet convolution `1 ⍟ (χ ·)` (via `chiRe_ofReal` on each divisor), then
`LSeries_convolution'` splits it into `LSeries 1 · LSeries (χ ·) = ζ · L(·,χ)`. -/
theorem dhLSeries_identity [NeZero q] (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (dhA χ n : ℂ)) s
      = riemannZeta s * DirichletCharacter.LFunction χ s := by
  have hcoeff : (fun n => (dhA χ n : ℂ)) = (1 : ℕ → ℂ) ⍟ (fun n => χ (n : ZMod q)) := by
    funext n
    simp only [LSeries.convolution_def, Pi.one_apply, one_mul]
    rw [Nat.sum_divisorsAntidiagonal' (fun _ b => χ (b : ZMod q))]
    unfold dhA
    push_cast
    exact Finset.sum_congr rfl fun d _ => chiRe_ofReal χ hsq d
  rw [hcoeff, LSeries_convolution' (LSeriesSummable_one_iff.mpr hs)
      (χ.LSeriesSummable_of_one_lt_re hs), LSeries_one_eq_riemannZeta hs,
      ← DirichletCharacter.LFunction_eq_LSeries χ hs]

/-! ## M3 / M4 — the named obstruction (the contour bookkeeping, PROSE, not `sorry`)

M1 (`dhLSeries_identity` + `dhDetector_mellin`) and M2 (`dhDetector_floor`,
`dhDetector_pos`) are LANDED above. M3 (the upper contour) and M4 (the balance +
inversion) are the multi-session core; below is the precise obstruction map so the
next session resumes without re-deriving it. The target contract is (constants FREE):

```
theorem dh_repulsion : ∃ b c k : ℝ, 0 < b ∧ 0 < c ∧ 0 ≤ k ∧
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → χ^2 = 1 → 2 ≤ q →
    ∀ β₀ : ℝ, LFunction χ β₀ = 0 → 1/2 < β₀ → β₀ < 1 →
    ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ.im ≠ 0 → |ρ.im| ≤ 1 →
      9/10 ≤ ρ.re → ρ.re < 1 →
      (1 - β₀) ≥ c * (q * (|ρ.im| + 2) : ℝ)^(-(b * (1 - ρ.re)))
                    / (Real.log (q * (|ρ.im| + 2)) + 2)^k
```

### M3 — what it needs, and exactly where it fights

The zero-detecting (SHIFTED) detector is
`D_ρ(x,N) = Σ_{n≤N} a(n)·w_z(n)·n^{−ρ}·(1−n/x)₊`;
its Mellin form is `D_ρ = (1/2πi)∫_{(c)} F(s+ρ)·G(s+ρ)·x^s/(s(s+1)) ds` (Benli Prop 5.1),
with `F(s) = ζ(s)·L(s,χ₁)` (= `dhLSeries_identity`) and `G` the finite Graham polynomial.
The UNSHIFTED case (`ρ = 0`) is `dhDetector_mellin` above — exact and summability-free.
The shift by `ρ` is a translation of the Dirichlet-polynomial argument (mechanical). The
contour shift `Re s = c > 1 → Re s = 1/2 − β` (via `ContourShift.rectBI` on a tall
rectangle) collects three pieces:

1. **The pole at `s = 1 − ρ`** (from `ζ`'s pole at `s = 1` inside `F(s+ρ)`): residue
   `≍ L(1,χ₁)·G(1)·x^{1−ρ}/((1−ρ)(2−ρ))`. LANDED: `ContourShift.kernel_residue`
   (probe-verified at a COMPLEX pole `β`); `Res_{s=1} ζ = 1`; `G(1,χ₁) = G(1,χ₀)` with the
   crude `G`-value bound `GrahamWeights.abs_sum_grahamTheta_div_le`.
   **THE FIGHT (algebraic seam):** `kernel_residue` handles a SIMPLE pole `1/(s−β)`; the
   `ζ`-pole must first be isolated as `ζ(s+ρ) = 1/(s+ρ−1) + (holomorphic)`, so that the
   residue carries `L(1,χ₁)` in its holomorphic factor. This Laurent split of `ζ` at `1`
   (mathlib `riemannZeta` residue) threaded through the finite `G` is the missing step.

2. **The `s = 0` term** `F(ρ)·G(ρ)·x^0` — VANISHES because `L(ρ,χ₁) = 0 ⟹ F(ρ) = 0`
   (THE VANISHING CONSUMED; this is DH-2a's diagonal insight, now benign because the
   PRODUCT frame makes the ζ-side harmless — the ζ-factor's `s=1−ρ` pole is item 1, not a
   competitor here). No Lean obstruction: it is `F(ρ) = 0` fed to the residue bookkeeping.

3. **The shifted-line integral `J` on `Re s = 1/2 − β`**: `|J| ≲ (Graham σ-sum)·(growth)·
   x^{1/2−β}·polylog`. LANDED footholds: `Growth.LFunction_growth` (`Re ≥ 1/2`,
   convexity-grade, constants free) for `L(1/2+it,χ)` and `L(1/2+it,χχ₁)`;
   `GrahamWeights.sum_abs_grahamTheta_rpow_le` (the σ-weighted `G`-sum);
   `StripConvergence.norm_LFunction_sub_partial_le_strip` (DH-STRIP tails);
   `ZeroCountNearOne.LFunction_zero_count_near_one` (enumerating near-1 zeros).
   **THE FIGHT (assembly):** the horizontal-edge integrals of `rectBI` must vanish as the
   rectangle height → ∞ (uniform-in-`t` product growth `F·G`, Benli Lem 4.3 + (5.7)–(5.17));
   `F(s)G(s)` must be shown to continue past `Re = 1` (`F = ζ·L` continues; `G` entire).
   ~several hundred lines of uniform integral estimates — the genuine multi-session bulk.

### M4 — the balance + inversion (`DH-4`; folds in once M3 lands)

From `|D_ρ| ≤ |residue| + |J|` (M3) and reverse-triangle floor `|D_ρ| ≥ 1 − 1/N − S₀`
(Benli (5.4)–(5.5), whose `n = 1` core is `dhDetector_floor`): balancing at
`log x ≍ log(q(|γ|+2))` gives `L(1,χ₁) ≳ x^{−b(1−β)}/polylog`. Then
`SiegelClose.LFunction_one_re_le_mvt_sharp` (`(L(1,χ)).re ≤ (1−β₀)·25e(1+log f)²`)
INVERTS this to the target lower bound on `1 − β₀` — the reversed Jutila-(1.10) shape.

### Route variant chosen for M3

The frozen design offers a fallback: "the vertical-line-only version (no shift; direct
estimation at `Re = 1+1/log x`)". The PRODUCT-frame analysis above (full `rectBI` shift) is
the primary route because item 2's vanishing is what makes the ζ-side harmless — precisely
the property DH-2a's single-detector route lacked. The vertical-only variant is retained as
the fallback if the horizontal-edge control (item 3's fight) proves intractable; it trades
the clean residue for a direct `Re = 1 + 1/log x` estimate against the zero-damped detector.

### Honesty (HB-ENGINE, R4)

NO twin claim. `dh_repulsion` is one input to WP2 (the `L′/L`/Prachar + density + repulsion
chain), itself gated behind R4 (beyond-level-½ / Kloosterman — the documented death rung).
-/

end Salt.SW

end
