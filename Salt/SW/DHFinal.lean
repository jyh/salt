/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.MoebiusLog

/-!
# The Deuring–Heilbronn repulsion's last node: the shifted truncation balance (HB-ENGINE, DH-FINAL)

Design: `docs/exploration/s3-hb3-design.md`, "DH-2b — THE PRODUCT-DETECTOR FREEZE".
Source: Benlİ–Goel–Twiss–Zaman, arXiv:2410.06082, §5 (the balance for Theorem 1.3 / Prop 5.1).

This is the endgame assembly. Every supplier is landed:
* `DHMain.dhDetectorShift` / `dhDetectorShift_mellin` — the ρ-twisted finite detector
  `D_ρ = Σ_{n≤N} dhCoeff(n)·n^{−ρ}·(1−n/x)₊` and its exact finite Mellin representation.
* `MoebiusLog.abs_sum_grahamTheta_div_le_inv_log` — the SHARP Barban–Vehov value bound
  `|Σ_{d≤z} θ_d/d| ≤ C/log z` (landed this cycle).
* `DHClose.LFunction_one_re_ge_partial` — the UNSHIFTED truncation balance template.
* `DHContour.rectBI_zeta_shift_mul` — the shifted residue at `s = 1−ρ`.
* `StripConvergence.norm_LFunction_sub_partial_le_strip` — the strip tails on `0 < Re ≤ 1`.
* `DHBalance.dh_repulsion_of_LFunction_one_lower` (M4) — the Siegel-MVT inversion.

## What lands here (Rung 1 of the shifted ladder — all sorry-free, axiom-clean)

The shifted-frame analog of the entire `DHRepulsion.dhDetector_floor` /
`DHClose.dhDetector_floor_explicit` competing-LOWER-estimate layer, plus the sharp
Graham-value bridge at the pole that carries tonight's Barban–Vehov cancellation into the
analytic DH layer. FINITE sums throughout (catch #61 — no integrability wall).

* **`dhCoeff_one`** — the `n = 1` seam `dhCoeff χ z 1 = 1` (`dhA(1)·(Σ_{d∣1}θ_d)² = 1·1`).
* **`norm_dhDetectorShift_term`** — the per-term norm identity
  `‖dhCoeff(n)·n^{−ρ}·(1−n/x)₊‖ = |dhCoeff(n)|·n^{−Re ρ}·(1−n/x)₊` (on `Re ρ > 0`).
* **`dhDetectorShift_eq_add_tail`** — the `n = 1` extraction: for `x > 1`,
  `D_ρ = (1 − 1/x) + Σ_{2≤n≤N} dhCoeff(n)·n^{−ρ}·(1−n/x)₊` (the `n=1` term is real, `1−1/x`).
* **`norm_dhDetectorShift_ge`** — THE SHIFTED FLOOR (evaluation (A) of the balance): the
  reverse-triangle competing LOWER estimate
  `(1 − 1/x) − Σ_{2≤n≤N} |dhCoeff(n)|·n^{−Re ρ}·(1−n/x)₊ ≤ ‖D_ρ‖`.
  The `ρ`-shifted analog of `dhDetector_floor_explicit`; the honest FINITE floor.
* **`dhGlin_one_eq`** — the Graham polynomial at the pole `s = 1`:
  `G₁(z,1) = Σ_{d≤z} θ_d/d` (as a real scalar cast to `ℂ`).
* **`norm_dhGlin_one_le`** — the SHARP Graham-value bound at the pole:
  `∃ C > 0, ∀ z ≥ 3, ‖G₁(z,1)‖ ≤ C/log z`, from tonight's `abs_sum_grahamTheta_div_le_inv_log`.
  The residue term at `s = 1−ρ` carries `G(1−ρ)`; as `Re ρ → 1` this is `G(1)`, and THIS is
  where the mollifier's `1/log z` cancellation enters the balance (the sharp `≍ 1/log z` gain,
  not the crude `norm_dhGpoly_le`'s `z^{1−σ}(1+log z)`).
* **`norm_dhGpoly_one_le`** — the squared form `∃ C > 0, ∀ z ≥ 3, ‖G(z,1)‖ ≤ (C/log z)²`.

## The residual (Rung 2/3, precisely named — PROSE, not `sorry`)

The floor (evaluation (A)) is landed. The CONTRADICTION shape (Benli §5) needs the SECOND
evaluation (B) of `D_ρ` via the residue at `s = 1−ρ`, whose holomorphic factor carries
`L(1,χ)·G(1−ρ)·x^{1−ρ}` — the `x^{−b(1−Re ρ)}` damping. Composed with the floor this forces
`L(1,χ) ≳ x^{−b(1−Re ρ)}/polylog`, which `dh_repulsion_of_LFunction_one_lower` (M4) inverts to
the `dh_repulsion` target. TWO independent obstructions block evaluation (B), both multi-session:

1. **The shifted-line integral `J` does not converge** (inherited; `DHBalance.norm_dhIntegrand_le`
   note). The corpus's `ζ` and `L` growth are each `O(|t|)`, product `O(|t|²)`, and the kernel
   decay only `O(|t|⁻²)`, leaving an `O(1)` non-integrable integrand. The honest route is the
   finite-`N` truncation (staying FINITE, catch #61): bound `‖D_ρ − residue‖` via
   `norm_LFunction_sub_partial_le_strip` at the single shifted frame `Re s = 1/2 − β`,
   optimizing `N ≍ x`. `rectBI_zeta_shift_mul` supplies the residue; the finite line-integral
   error still needs the several-hundred-line uniform-in-`t` product-growth bookkeeping.
2. **The finite tail `Σ_{2≤n≤N} |dhCoeff(n)|·n^{−Re ρ}·(1−n/x)₊`** (subtracted in the floor) is
   NOT small termwise; making it `o(main)` requires the lcm-collection regroup of the Graham
   double sum `Σ_{m∣n}(Σ_{lcm(d,e)=m} θ_d θ_e)` (the NAMED `GrahamWeights` residual (1)) fed
   through the Barban–Vehov cancellation — again a genuine multi-session build.

`norm_dhGlin_one_le` closes the SHARP-`G`-at-the-pole prerequisite of obstruction 2; the
lcm-regroup and the finite-`N` `J`-truncation remain the two crux stones.

## Honesty / death map (HB-ENGINE, R4 — NO twin claim)

NOT a proof of the Twin Prime Conjecture. Delivers competing-estimate substrate for the
conditional `InfinitelyManySiegelZeros → TwinPrimeConjecture`; the death rung is R4.
-/

open Complex

noncomputable section

namespace Salt.SW

open Finset

/-! ## The `n = 1` seam and the per-term norm identity -/

/-- **The `n = 1` seam.** `dhCoeff χ z 1 = 1` (for `z ≥ 2`): `dhA(1)·(Σ_{d∣1}θ_d)² = 1·1`. -/
lemma dhCoeff_one {q : ℕ} (χ : DirichletCharacter ℂ q) {z : ℕ} (hz : 2 ≤ z) :
    dhCoeff χ z 1 = 1 := by
  rw [dhCoeff, dhA_one, dhWeightSq_one hz, mul_one]

/-- **The per-term norm identity.** On `Re ρ > 0` and `n ≥ 1`, the shifted detector's `n`-th
summand has norm `|dhCoeff(n)|·n^{−Re ρ}·(1−n/x)₊`. The `n^{−ρ}` twist contributes only
`n^{−Re ρ}` (real), and the coefficient/kernel are real-cast. -/
lemma norm_dhDetectorShift_term {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℕ) (x : ℝ)
    {ρ : ℂ} (hρ : 0 < ρ.re) {n : ℕ} (_hn : 1 ≤ n) :
    ‖(dhCoeff χ z n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ)‖
      = |dhCoeff χ z n| * (n : ℝ) ^ (-ρ.re) * dhKernR ((n : ℝ) / x) := by
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, norm_natCast_cpow_neg hρ n,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (dhKernR_nonneg _)]

/-! ## The `n = 1` extraction and the shifted floor (evaluation (A)) -/

/-- **The `n = 1` extraction.** For `x > 1`, `z ≥ 2`, `N ≥ 1`, the shifted detector splits off
its real `n = 1` term `(1 − 1/x)`:
`D_ρ = (1 − 1/x) + Σ_{2≤n≤N} dhCoeff(n)·n^{−ρ}·(1−n/x)₊`. -/
lemma dhDetectorShift_eq_add_tail {q : ℕ} (χ : DirichletCharacter ℂ q) {z : ℕ} (hz : 2 ≤ z)
    {x : ℝ} (hx : 1 < x) {N : ℕ} (hN : 1 ≤ N) (ρ : ℂ) :
    dhDetectorShift χ z x N ρ
      = ((1 - 1 / x : ℝ) : ℂ)
        + ∑ n ∈ Finset.Icc 2 N,
            (dhCoeff χ z n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ) := by
  have hins : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1 : (1 : ℕ) ∉ Finset.Icc 2 N := by simp only [Finset.mem_Icc]; omega
  rw [dhDetectorShift, hins, Finset.sum_insert h1]
  congr 1
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hle : (1 : ℝ) / x ≤ 1 := le_of_lt ((div_lt_one hx0).mpr hx)
  have h1x : dhKernR (((1 : ℕ) : ℝ) / x) = 1 - 1 / x := by
    rw [Nat.cast_one]; exact dhKernR_eq hle
  rw [dhCoeff_one χ hz, h1x, Nat.cast_one, Complex.one_cpow, mul_one, Complex.ofReal_one, one_mul]

/-- **THE SHIFTED FLOOR (evaluation (A)).** For a real character (`χ² = 1` not needed here — the
floor is norm-level), `x > 1`, `z ≥ 2`, `N ≥ 1`, `Re ρ > 0`, the shifted detector's norm is
bounded below by its `n = 1` term minus the shifted tail:
`(1 − 1/x) − Σ_{2≤n≤N} |dhCoeff(n)|·n^{−Re ρ}·(1−n/x)₊ ≤ ‖D_ρ‖`.
The `ρ`-shifted analog of `DHClose.dhDetector_floor_explicit`; the honest FINITE competing
LOWER estimate of the balance (reverse triangle on `dhDetectorShift_eq_add_tail`). -/
theorem norm_dhDetectorShift_ge {q : ℕ} (χ : DirichletCharacter ℂ q) {z : ℕ} (hz : 2 ≤ z)
    {x : ℝ} (hx : 1 < x) {N : ℕ} (hN : 1 ≤ N) {ρ : ℂ} (hρ : 0 < ρ.re) :
    (1 - 1 / x)
        - ∑ n ∈ Finset.Icc 2 N, |dhCoeff χ z n| * (n : ℝ) ^ (-ρ.re) * dhKernR ((n : ℝ) / x)
      ≤ ‖dhDetectorShift χ z x N ρ‖ := by
  set T : ℂ := ∑ n ∈ Finset.Icc 2 N,
      (dhCoeff χ z n : ℂ) * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / x) : ℝ) : ℂ) with hT
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have h1x : (0 : ℝ) ≤ 1 - 1 / x := by
    have : 1 / x ≤ 1 := le_of_lt ((div_lt_one hx0).mpr hx); linarith
  have hsplit := dhDetectorShift_eq_add_tail χ hz hx hN ρ
  -- reverse triangle inequality: ‖a‖ − ‖T‖ ≤ ‖a + T‖
  have hrev : ‖((1 - 1 / x : ℝ) : ℂ)‖ - ‖T‖ ≤ ‖((1 - 1 / x : ℝ) : ℂ) + T‖ := by
    have h := norm_sub_norm_le ((1 - 1 / x : ℝ) : ℂ) (-T)
    simpa [sub_neg_eq_add, norm_neg] using h
  have hnorma : ‖((1 - 1 / x : ℝ) : ℂ)‖ = 1 - 1 / x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1x]
  have hTle : ‖T‖ ≤ ∑ n ∈ Finset.Icc 2 N,
      |dhCoeff χ z n| * (n : ℝ) ^ (-ρ.re) * dhKernR ((n : ℝ) / x) := by
    rw [hT]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun n hn => ?_
    exact norm_dhDetectorShift_term χ z x hρ (by rw [Finset.mem_Icc] at hn; omega)
  rw [hnorma] at hrev
  rw [hsplit, ← hT]
  linarith [hrev, hTle]

/-! ## The sharp Graham-value bridge at the pole `s = 1` -/

/-- **The Graham polynomial at the pole.** `G₁(z,1) = Σ_{d≤z} θ_d/d` (as a real scalar cast to
`ℂ`): the value `dhGlin z 1` at the residue exponent, where the mollifier's cancellation lives. -/
lemma dhGlin_one_eq (z : ℕ) :
    dhGlin z 1 = ((∑ d ∈ Finset.Icc 1 z, grahamTheta z d / (d : ℝ) : ℝ) : ℂ) := by
  rw [dhGlin, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Complex.cpow_neg, Complex.cpow_one]
  push_cast
  ring

/-- **The SHARP Graham-value bound at the pole.** `∃ C > 0, ∀ z ≥ 3, ‖G₁(z,1)‖ ≤ C/log z`,
from tonight's `abs_sum_grahamTheta_div_le_inv_log`. The residue at `s = 1−ρ` carries `G(1−ρ)`;
as `Re ρ → 1` this becomes `G(1)`, and the sharp `1/log z` gain (over the crude
`norm_dhGpoly_le`) is exactly the mollifier's Barban–Vehov cancellation entering the balance. -/
lemma norm_dhGlin_one_le :
    ∃ C, 0 < C ∧ ∀ z : ℕ, 3 ≤ z → ‖dhGlin z 1‖ ≤ C / Real.log z := by
  obtain ⟨C, hC, hbound⟩ := abs_sum_grahamTheta_div_le_inv_log
  refine ⟨C, hC, fun z hz => ?_⟩
  rw [dhGlin_one_eq, Complex.norm_real, Real.norm_eq_abs]
  exact hbound z hz

/-- **The SHARP squared Graham-value bound at the pole.** `∃ C > 0, ∀ z ≥ 3,
‖G(z,1)‖ ≤ (C/log z)²`. Benli's factor `G = G₁²` at the residue exponent; the squared sharp
value bound is the `t`-independent `G`-side of the residue term of evaluation (B). -/
lemma norm_dhGpoly_one_le :
    ∃ C, 0 < C ∧ ∀ z : ℕ, 3 ≤ z → ‖dhGpoly z 1‖ ≤ (C / Real.log z) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := norm_dhGlin_one_le
  refine ⟨C, hC, fun z hz => ?_⟩
  rw [dhGpoly, norm_pow]
  have hlogz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  gcongr
  exact hbound z hz

end Salt.SW

end
