/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.LandauPage
import Salt.SW.EFSharpMult

/-!
# M-ONE — the multiplicity binder `hm1 : zeroMult χ β₀ = 1`, discharged at large `η`

The N4b design (`docs/exploration/n4b-design-0805.md` §D11) carries
`m := zeroMult χ (β₀ : ℂ)` explicitly through (L1)/(L2) and rules that the Lemma-3
cancellation is clean **only at `m = 1`** (for `m ≥ 2` the tail turns `F` into
`(ηL)^{−m}`, and `κS₁·(L′/L)²` scales like `(ηL)^{2−2m}`). The binder
`hm1 : zeroMult χ (β₀ : ℂ) = 1` therefore rides on W3/W4/(L2). This file discharges it
above an **absolute** `η`-threshold: `η ≥ 15000`, with `η := ((1−β₀)·log q)⁻¹` as in the
design's §0. No `q`-growth, no new hypotheses beyond primitivity and `χ ≠ 1`.

## 🔴 THE ROUTE — a design finding of this micro-node

D11's sketch proposed the **Prachar disc count**: two zeros (with multiplicity) in
`|s − 1| ≤ 2(1−β₀)` would force `2 ≤ C·(1 + 2/η)`, hoping the corpus constant kills it.
**That route is dead at any `η`, and the obstruction is structural, not a slack in our
constants.** The landed count (`Salt.SW.LFunction_zero_count_near_one`,
`Salt/SW/ZeroCountNearOne.lean:98`) reads

    count (closedBall 1 r) ≤ 7200·(1 + r·log(q+2)),

and as `r → 0` its right side tends to the *additive* constant `C = 7200`. A disc-count
contradiction against `m ≥ 2` needs that additive constant to be `< 2`; ours is `7200`,
and no `η`-threshold changes it (the guarded form
`LFunction_zero_count_near_one_guarded` is worse: it is `≥ 2C` on its own guard
`r ≥ 1/log(q+2)`). Sharpening the count is not a matter of arithmetic care either: the
additive `1` in Prachar's shape is exactly the mass of the counted zero itself, and
driving its coefficient below `2` **is** the optimized-radius Landau argument.

That argument is already in the kernel. `Salt.SW.landau_one_exceptional_at`
(`Salt/SW/LandauPage.lean:194`) evaluates the partial fraction at
`σ = 1 + (3/5000)/log(4q)` — the radius tuned so that the kept term of a
double zero, `2/(σ−β₀) ≥ 2500·log(4q)`, overruns the whole budget
`1/(σ−1) + 1 + 720·log(4q) = (5000/3 + 720)·log(4q) + 1`. It delivers
`analyticOrderAt (LFunction χ) β₀ = 1` for any real zero in the window
`1 − (1/5000)/log(4q) ≤ β₀`. M-ONE is then the bridge to `zeroMult` plus the
`η`-translation; the whole micro-node is three thin wrappers.

## The threshold, exactly

The window `(1−β₀)·log(4q) ≤ 1/5000` becomes, on `log 4 ≤ 2·log q` (i.e. `4 ≤ q²`,
valid for `q ≥ 2`), the sufficient gap condition `(1−β₀)·log q ≤ 1/15000`, i.e.

    η := ((1−β₀)·log q)⁻¹ ≥ 15000.

`15000 = 3·5000` is sharp *for this route at `q = 2`*; for `q ≥ 4` the same window reads
`η ≥ 10000`, and `η ≥ 5000·(1 + log 4/log q)` in general.

**Convention warning.** The threshold is stated against the design's §0 definition
`η := ((1−β₀)·log q)⁻¹`. Under the L-free reading `η := (1−β₀)⁻¹` the same window reads
`η ≥ 5000·log(4q)` — `q`-growing. Consumers must name which `η` they mean.

## Corpus consumed
* `Salt.SW.landau_one_exceptional_at` (S3e; the Landau two-term extraction at `c₁ = 1/5000`).
* `Salt.SW.zeroMult_eq_one` (`analyticOrderAt = 1 → zeroMult = 1`).
* `DirichletCharacter.LFunction_ne_zero_of_one_le_re` (for `β₀ < 1`).
-/

namespace Salt.HB

open Complex DirichletCharacter Salt.SW

/-! ## 1. The window form (the sharpest statement) -/

/-- **M-ONE, window form.** For a primitive `χ ≠ 1` mod `q`, a real zero `β₀` of `L(·,χ)` in
Landau's exceptional window `1 − (1/5000)/log(4q) ≤ β₀` has multiplicity exactly `1`:
`zeroMult χ (β₀ : ℂ) = 1`. This is `landau_one_exceptional_at`'s simplicity half, read in
the `zeroMult` currency the N4b waves carry. -/
theorem zeroMult_eq_one_of_window {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {β₀ : ℝ}
    (hz : LFunction χ (β₀ : ℂ) = 0)
    (hw : 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) ≤ β₀) :
    zeroMult χ (β₀ : ℂ) = 1 :=
  zeroMult_eq_one (landau_one_exceptional_at hχ hχ1 hz hz hw hw).2

/-! ## 2. The gap form and the `η` form -/

/-- `2 ≤ q` for a primitive `χ ≠ 1` mod `q` (conductor `= q ≠ 1`, and `q ≠ 0`). -/
private lemma two_le_of_primitive_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) : 2 ≤ q := by
  have hcond : χ.conductor = q := hχ
  have hc1 : χ.conductor ≠ 1 := fun h => hχ1 (eq_one_iff_conductor_eq_one.mpr h)
  rw [hcond] at hc1
  have hqne0 : q ≠ 0 := NeZero.ne q
  omega

/-- **M-ONE, gap form.** `(1−β₀)·log q ≤ 1/15000` suffices for simplicity of the real zero
`β₀`. Route: `log(4q) = log 4 + log q ≤ 3·log q` for `q ≥ 2`, so the hypothesis implies
Landau's window `(1−β₀)·log(4q) ≤ 1/5000`. -/
theorem zeroMult_eq_one_of_gap {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {β₀ : ℝ}
    (hz : LFunction χ (β₀ : ℂ) = 0)
    (hgap : (1 - β₀) * Real.log (q : ℝ) ≤ 1 / 15000) :
    zeroMult χ (β₀ : ℂ) = 1 := by
  have hq2 : 2 ≤ q := two_le_of_primitive_ne_one hχ hχ1
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  -- `β₀ < 1`: `L(·,χ)` has no zero on `Re s ≥ 1` for `χ ≠ 1`
  have hβ1 : β₀ < 1 := by
    by_contra hc
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1)
      (by rw [Complex.ofReal_re]; linarith) hz
  have hgap0 : (0 : ℝ) < 1 - β₀ := by linarith
  -- `log 4 ≤ 2·log q`, so `log(4q) ≤ 3·log q`
  have hlogq : Real.log 2 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) hqR
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogqpos : (0 : ℝ) < Real.log (q : ℝ) := lt_of_lt_of_le hlog2pos hlogq
  have hlog4 : Real.log (4 * (q : ℝ)) = 2 * Real.log 2 + Real.log (q : ℝ) := by
    rw [Real.log_mul (by norm_num) (by linarith), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast; ring
  have hlog4le : Real.log (4 * (q : ℝ)) ≤ 3 * Real.log (q : ℝ) := by rw [hlog4]; linarith
  have hlog4pos : (0 : ℝ) < Real.log (4 * (q : ℝ)) := by rw [hlog4]; linarith
  -- the window
  refine zeroMult_eq_one_of_window hχ hχ1 hz ?_
  have hkey : (1 - β₀) * Real.log (4 * (q : ℝ)) ≤ 1 / 5000 := by
    calc (1 - β₀) * Real.log (4 * (q : ℝ))
        ≤ (1 - β₀) * (3 * Real.log (q : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hlog4le hgap0.le
      _ = 3 * ((1 - β₀) * Real.log (q : ℝ)) := by ring
      _ ≤ 3 * (1 / 15000) := by linarith
      _ = 1 / 5000 := by norm_num
  have := (le_div_iff₀ hlog4pos).mpr hkey
  linarith

/-- **M-ONE, the `η` form — the deliverable.** With the design's `η := ((1−β₀)·log q)⁻¹`
(`docs/exploration/n4b-design-0805.md` §0), the binder `hm1` is discharged above the
**absolute** threshold `η ≥ 15000`:

    η ≥ 15000  →  zeroMult χ (β₀ : ℂ) = 1.

No `q`-growth: unlike the `hN`/`hN+` regime thresholds of the same design, `15000` is a
bare numeral. -/
theorem zeroMult_eq_one_of_eta {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {β₀ η : ℝ}
    (hz : LFunction χ (β₀ : ℂ) = 0)
    (hη : η = ((1 - β₀) * Real.log (q : ℝ))⁻¹)
    (hbig : 15000 ≤ η) :
    zeroMult χ (β₀ : ℂ) = 1 := by
  have hq2 : 2 ≤ q := two_le_of_primitive_ne_one hχ hχ1
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hβ1 : β₀ < 1 := by
    by_contra hc
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1)
      (by rw [Complex.ofReal_re]; linarith) hz
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogqpos : (0 : ℝ) < Real.log (q : ℝ) :=
    lt_of_lt_of_le hlog2pos (Real.log_le_log (by norm_num) hqR)
  have hdpos : (0 : ℝ) < (1 - β₀) * Real.log (q : ℝ) :=
    mul_pos (by linarith) hlogqpos
  refine zeroMult_eq_one_of_gap hχ hχ1 hz ?_
  have hdinv : (1 - β₀) * Real.log (q : ℝ) = η⁻¹ := by rw [hη, inv_inv]
  rw [hdinv, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hbig

end Salt.HB
