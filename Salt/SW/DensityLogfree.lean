/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.DensityCrude
import Salt.SW.WellSpacedAt

/-!
# ARM B part B2, wave **W0** — the LOG-FREE density on the LOW strip `4/5 ≤ σ ≤ 119/120`

B2 is the log-free zero-density input `N(σ,T,χ) ≤ C·(qT)^{D(1−σ)}` on `4/5 ≤ σ ≤ 1`
with `D ≤ 150`. Jutila's §3 — the analytic half — **does not cover the whole range**:
his §3 opens *"For 4/5 ≤ α ≤ 1−ε the assertions follow from [6]; hence we may suppose
that α ≥ 1−ε"*. That delegation is FREE here at `ε = 1/120`: on the low strip the
landed **count** `zeroCountM_le` already beats the target, because the exponent
`150(1−σ)` is at least `5/4` there and the count is `≍ T·log(qT)`.

## What this file carries

* `zeroCountM_density_logfree_low` — `N(σ,T,χ) ≤ 1378·(qT)^{150(1−σ)}` on
  `4/5 ≤ σ ≤ 119/120`, `T ≥ 2`, `q ≥ 2`, for a primitive `χ`.

## What this file does NOT cover

The near-1 strip **`119/120 < σ ≤ 1`** — that is B2's own strip (Jutila §3 specialised
to a single `χ` at `ε = 1/120`), landed by wave **W9f**, and the `σ = 1` line there is
its own case (the count is `0` by `LFunction_ne_zero_of_one_le_re`). The glue
`D := 150` for both halves is W9f's as well.

**The cut is exactly tight.** `150(1 − σ) ≥ 5/4 ⟺ σ ≤ 119/120`: the low half needs the
exponent to pay for a count that grows like `T^{5/4}` after the log is absorbed, and
`150·(1/120) = 5/4` on the nose. Neither the literal `1378` nor the split point has
slack to give: raising `σ` past `119/120` drops the exponent below `5/4` and the count
route dies at once.

**Log-freeness (F6).** No `log` survives outside the exponent: the count's
`log(q(T+3))` is absorbed by `log y ≤ 4(y^{1/4} − 1) ≤ 4·y^{1/4}` (`Real.log_rpow` at
`y^{1/4}` and `Real.log_le_sub_one_of_pos`), which is what makes the statement
*log-free* rather than the landed `zeroCountM_density_log`'s explicit-count shape.

**`q ≥ 3` is forced, so `q = 2` is vacuous.** Under `χ.IsPrimitive ∧ 2 ≤ q`,
`ne_one_of_isPrimitive` (`Growth.lean:271`) gives `χ ≠ 1` and `three_le_of_ne_one`
(`CrownTheorem1.lean:5540`) gives `3 ≤ q` — mod 1 and mod 2 the only character is `1`.
The `q = 2` numeral row below is therefore a **two-real inequality check** on the two
sides of the bound at the worst corner, never an instantiation at a character.
-/

open Complex DirichletCharacter Filter Set Metric Function

namespace Salt.SW

/-- **B2 · W0 — the low strip, log-free.**

    N(σ, T, χ) ≤ 1378·(qT)^{150(1−σ)}      for  4/5 ≤ σ ≤ 119/120,  T ≥ 2,  q ≥ 2.

The proof is the landed count `zeroCountM_le` (`N ≤ 137·(2T+3)·log(q(T+3))`) with the
two crudities taken at their **sharp** form at `T ≥ 2` — `2T + 3 ≤ 3.5T` and
`T + 3 ≤ 2.5T`, both tight at `T = 2` — and the log absorbed by
`log y ≤ 4(y^{1/4} − 1) ≤ 4·y^{1/4}`:

    N ≤ 137·(3.5T)·4·(2.5·qT)^{1/4} = 137·3.5·4·2.5^{1/4}·q^{1/4}T^{5/4} ≤ 2494·q^{1/4}T^{5/4}

(using `2.5^{1/4} ≤ 1.3`, since `1.3⁴ = 2.8561 ≥ 2.5`), and `2494 ≤ 1378·q` at `q ≥ 2`
turns `q^{1/4}T^{5/4}` into `1378·(qT)^{5/4}`. The last step is
`(qT)^{5/4} ≤ (qT)^{150(1−σ)}` at `qT ≥ 1`, which is exactly `σ ≤ 119/120`.

The COARSE chain (`2T + 3 ≤ 4T`, `T + 3 ≤ 3T`, the shape of `zeroCountM_density_crude`)
would give `137·4·4·3^{1/4} = 2884.83` and need `C ≥ 1442.42` at `q = 2` — it misses
`1378` by 4.7 %. The chain sharpens; **the literal `1378` is not raised.** -/
theorem zeroCountM_density_logfree_low {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (σ T : ℝ) (hσ1 : 4 / 5 ≤ σ) (hσ2 : σ ≤ 119 / 120)
    (hT : 2 ≤ T) :
    zeroCountM χ σ T ≤ 1378 * ((q : ℝ) * T) ^ (150 * (1 - σ)) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hQ4 : (4 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hQ0 : (0 : ℝ) < (q : ℝ) * T := by linarith
  have hQ1 : (1 : ℝ) ≤ (q : ℝ) * T := by linarith
  -- the landed count, at the numeral `137` (this is where `4/5 ≤ σ` is spent, via `1/2 ≤ σ`)
  have hcount := zeroCountM_le χ hχ hq (by linarith : (1 : ℝ) / 2 ≤ σ) hT0
  have hlognn : 0 ≤ Real.log ((q : ℝ) * (T + 3)) := by
    refine Real.log_nonneg ?_
    nlinarith
  have hA0 : (0 : ℝ) < ((q : ℝ) * T) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hQ0 _
  -- the SHARPENED crudity `T + 3 ≤ 2.5·T` (tight at `T = 2`), inside the log
  have hlog1 : Real.log ((q : ℝ) * (T + 3)) ≤ Real.log (2.5 * ((q : ℝ) * T)) := by
    refine Real.log_le_log (by nlinarith) ?_
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (q : ℝ)) (by linarith : (0 : ℝ) ≤ T - 2)]
  -- the rpow step: `log y ≤ 4(y^{1/4} − 1) ≤ 4·y^{1/4}`
  have hy0 : (0 : ℝ) < 2.5 * ((q : ℝ) * T) := by linarith
  have hquarter : Real.log (2.5 * ((q : ℝ) * T))
      ≤ 4 * ((2.5 : ℝ) ^ (1 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 4 : ℝ)) := by
    have hpos : (0 : ℝ) < (2.5 * ((q : ℝ) * T)) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hy0 _
    have h1 := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_rpow hy0, Real.mul_rpow (by norm_num) hQ0.le] at h1
    linarith
  -- `2.5^{1/4} ≤ 1.3`, since `1.3⁴ = 2.8561 ≥ 2.5`
  have hcst : (2.5 : ℝ) ^ (1 / 4 : ℝ) ≤ 1.3 := by
    have h1 : (2.5 : ℝ) ≤ (1.3 : ℝ) ^ (4 : ℕ) := by norm_num
    have h2 : (2.5 : ℝ) ^ (1 / 4 : ℝ) ≤ ((1.3 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
    have h3 : ((1.3 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) = 1.3 := by
      rw [← Real.rpow_natCast (1.3 : ℝ) 4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1.3)]
      norm_num
    rw [h3] at h2
    exact h2
  have hL4 : Real.log ((q : ℝ) * (T + 3)) ≤ 4 * (1.3 * ((q : ℝ) * T) ^ (1 / 4 : ℝ)) := by
    have hmul : (2.5 : ℝ) ^ (1 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 4 : ℝ)
        ≤ 1.3 * ((q : ℝ) * T) ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_right hcst hA0.le
    linarith
  -- the SHARPENED crudity `2T + 3 ≤ 3.5·T` (tight at `T = 2`), outside the log
  have hstep1 : 137 * (2 * T + 3) * Real.log ((q : ℝ) * (T + 3))
      ≤ 137 * (3.5 * T) * Real.log ((q : ℝ) * (T + 3)) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1.5 * T - 3) hlognn]
  have hstep2 : 137 * (3.5 * T) * Real.log ((q : ℝ) * (T + 3))
      ≤ 137 * (3.5 * T) * (4 * (1.3 * ((q : ℝ) * T) ^ (1 / 4 : ℝ))) :=
    mul_le_mul_of_nonneg_left hL4 (by linarith)
  -- `137·3.5·4·1.3 = 2493.4 ≤ 2756 = 1378·2 ≤ 1378·q`
  have hstep3 : 137 * (3.5 * T) * (4 * (1.3 * ((q : ℝ) * T) ^ (1 / 4 : ℝ)))
      ≤ 1378 * (((q : ℝ) * T) * ((q : ℝ) * T) ^ (1 / 4 : ℝ)) := by
    nlinarith [mul_nonneg (mul_nonneg hT0 hA0.le) (by linarith : (0 : ℝ) ≤ (q : ℝ) - 2),
      mul_nonneg hT0 hA0.le]
  have hpow : ((q : ℝ) * T) ^ (5 / 4 : ℝ)
      = ((q : ℝ) * T) * ((q : ℝ) * T) ^ (1 / 4 : ℝ) := by
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hQ0, Real.rpow_one]
  -- the exponent: `5/4 ≤ 150(1 − σ)` is EXACTLY `σ ≤ 119/120`
  have hmono : ((q : ℝ) * T) ^ (5 / 4 : ℝ) ≤ ((q : ℝ) * T) ^ (150 * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  calc zeroCountM χ σ T
      ≤ 137 * (2 * T + 3) * Real.log ((q : ℝ) * (T + 3)) := hcount
    _ ≤ 1378 * (((q : ℝ) * T) * ((q : ℝ) * T) ^ (1 / 4 : ℝ)) := by linarith
    _ = 1378 * ((q : ℝ) * T) ^ (5 / 4 : ℝ) := by rw [hpow]
    _ ≤ 1378 * ((q : ℝ) * T) ^ (150 * (1 - σ)) := by linarith

-- **W0's exit-test numeral row (a)**, at the worst corner `σ = 119/120`, `q = 2`, `T = 2`:
-- the count's side is `137·(2·2+3)·log(2·(2+3)) = 137·7·log 10 = 2208.18` and the bound's
-- side is `1378·(2·2)^{150(1−119/120)} = 1378·4^{5/4} = 7795.15`. A TWO-REAL check: `q = 2`
-- is vacuous under `IsPrimitive ∧ 2 ≤ q` (`3 ≤ q` is forced), so this is never an
-- instantiation at a character. Proved with room to spare: `log 10 = 2·log √10 ≤ 2(√10 − 1)
-- ≤ 4.326` puts the left side under `4149`, and `4^{5/4} ≥ 4^1` puts the right side over
-- `5512`.
example : (137 : ℝ) * 7 * Real.log 10 ≤ 1378 * (4 : ℝ) ^ (5 / 4 : ℝ) := by
  have hs2 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 10 ≤ 3.163 := by nlinarith [Real.sqrt_nonneg 10]
  have hlog : Real.log 10 ≤ 4.326 := by
    have h1 : Real.log (Real.sqrt 10) ≤ Real.sqrt 10 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_sqrt (by norm_num)] at h1
    linarith
  have h4 : (4 : ℝ) ≤ (4 : ℝ) ^ (5 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (by norm_num : (1 : ℝ) ≤ 5 / 4)
    rwa [Real.rpow_one] at h
  nlinarith

/-! ## 4. The boxes at the scale `Δ = 1/log D` (B2 W9e — W1 at height per box, the representatives)

The count `N(σ, T, χ)` is fibred over the boxes `[σ, 1] × [kΔ, (k+1)Δ)`, `Δ := 1/log D`,
`k ∈ [−⌈T log D⌉ − 1, ⌈T log D⌉ + 1]` (`zeroCountM_eq_sum_boxFibre`); each box sits in the disc
`closedBall (1 + (k + ½)Δ·I) r` with `r = Δ·√(λ² + ¼)`, `λ := (1 − σ) log D`
(`boxFibre_subset_closedBall` — no strip binder is needed for the geometry, and `r < 1/2` on
the strip `119/120 ≤ σ` for every `D > 2.72`); W1 at height counts the disc — with W1's constant
THREADED as the binder `hC₁` (W1 is `∃ C`; its proof's witness `7200` is never a row here):
`count ≤ C₁·(1 + r·log(q + |t₀| + 2)) ≤ C₁·(7/4 + 3λ/2)` on `D = qT ≥ 10²⁰`, `T ≥ 2`, since
`|t₀| ≤ T + 2.5/log D ≤ T + 1` and `log(q + T + 3) ≤ (3/2)·log(qT)` at `q ≥ 2` (margin `+0.134` at
`(2, 2)`), `√(λ² + ¼) ≤ λ + ½` (`efMultTotal_boxFibre_le`). ONE representative per box, TOTAL
(`boxRep`, the Skolem def; `boxRep_mem`); the representatives of the boxes of one PARITY are
`Δ`-well-spaced — boxes `k ≠ k'` of the same parity have `|k − k'| ≥ 2`, so the gap is strictly
`> (|k − k'| − 1)Δ ≥ Δ` (`wellSpacedAt_parity_reps`, one row at `c = 0, 1`); and the count is at
most the box bound times the number of NON-EMPTY boxes, the even ones plus the odd ones
(`zeroCountM_le_box_bound_mul`). W9f reads the last row with W9c's ratio. Both count rows carry
`σ ≤ 1` beside the strip's `119/120 ≤ σ`: above `1` the box is EMPTY and the bound `C₁(7/4 + 3λ/2)`
is NEGATIVE for `λ < −7/6` — an enumeration of the binders PRESENT could not see the missing one.

The measured receipts (design v2 §A.1, receipt (e) as corrected at the pass): at `D = 10²⁰` on
the strip `λ ≤ log D/120 = 0.384` and `r ≤ 1.37·10⁻²`; `C₁(1 + r·(3/2)log D)` against
`C₁(7/4 + 3λ/2)` reads `1.75 / 2.06 / 2.68` against `1.75 / 2.50 / 3.25` at `λ = 0, ½, 1` (per
unit `C₁`); `(3/2)log(qT) − log(q + T + 3) = 0.1335` at `(q, T) = (2, 2)`, `0.6082` at `(3, 2)`;
`2.5/log D ≤ 1` from `D ≥ e^{2.5} = 12.2`; the shape `7/4 + 3λ/2 ≤ (7/4)e^{λ}` at `λ = 0`
(equality) and `λ = 1` (`3.25 ≤ 4.76`). The literal `12,600 = 7200·7/4` of the design's v1 is a
docstring number, not a row (the verdict's kill 5). -/

/-- The box index of an ordinate at the scale `Δ = 1/log D`: `k = ⌊Im ρ · log D⌋`. -/
noncomputable def boxIndex (D : ℝ) (ρ : ℂ) : ℤ := ⌊ρ.im * Real.log D⌋

/-- The zeros of the `k`-th box: those of `boxZeros χ σ 1 T` with `boxIndex D ρ = k`. -/
noncomputable def boxFibre {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T D : ℝ)
    (k : ℤ) : Finset ℂ :=
  (boxZeros χ σ 1 T).filter (fun ρ => boxIndex D ρ = k)

/-- ONE representative per box, TOTAL: the Skolem def — `Exists.choose` on `Finset.Nonempty`
(which IS `∃ x, x ∈ s`; `Finset.Nonempty.choose` has no hits in mathlib), `0` on an empty box. -/
noncomputable def boxRep {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T D : ℝ)
    (k : ℤ) : ℂ :=
  if h : (boxFibre χ σ T D k).Nonempty then h.choose else 0

theorem boxRep_mem {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {σ T D : ℝ} {k : ℤ}
    (h : (boxFibre χ σ T D k).Nonempty) : boxRep χ σ T D k ∈ boxFibre χ σ T D k := by
  have hd : boxRep χ σ T D k
      = if h : (boxFibre χ σ T D k).Nonempty then h.choose else 0 := rfl
  rw [hd, dif_pos h]
  exact h.choose_spec

/-- The index range covers the box `|Im ρ| ≤ T` (one unit of slack at each end). -/
theorem boxIndex_mem_Icc {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    {σ T D : ℝ} (hD : 1 < D) {ρ : ℂ} (hρ : ρ ∈ boxZeros χ σ 1 T) :
    boxIndex D ρ ∈ Finset.Icc (-⌈T * Real.log D⌉ - 1) (⌈T * Real.log D⌉ + 1) := by
  have him : |ρ.im| ≤ T := ((mem_boxZeros hχ1).mp hρ).2.2.2
  have hL : 0 < Real.log D := Real.log_pos hD
  have habs : |ρ.im * Real.log D| ≤ T * Real.log D := by
    rw [abs_mul, abs_of_pos hL]
    exact mul_le_mul_of_nonneg_right him hL.le
  have hb := abs_le.mp habs
  have hce : T * Real.log D ≤ ((⌈T * Real.log D⌉ : ℤ) : ℝ) := Int.le_ceil _
  have hbi : boxIndex D ρ = ⌊ρ.im * Real.log D⌋ := rfl
  rw [Finset.mem_Icc, hbi]
  refine ⟨?_, ?_⟩
  · rw [Int.le_floor]
    push_cast
    linarith [hb.1]
  · have hlt : ⌊ρ.im * Real.log D⌋ < ⌈T * Real.log D⌉ + 2 := by
      rw [Int.floor_lt]
      push_cast
      linarith [hb.2]
    omega

/-- THE FIBRING: the count is the sum of the boxes' counts (`Finset.sum_fiberwise_of_maps_to`
on the template `efMultTotal_box_le`). -/
theorem zeroCountM_eq_sum_boxFibre {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    {σ T D : ℝ} (hD : 1 < D) :
    zeroCountM χ σ T
      = ∑ k ∈ Finset.Icc (-⌈T * Real.log D⌉ - 1) (⌈T * Real.log D⌉ + 1),
          efMultTotal χ (boxFibre χ σ T D k) := by
  have hmaps : ∀ ρ ∈ boxZeros χ σ 1 T,
      boxIndex D ρ ∈ Finset.Icc (-⌈T * Real.log D⌉ - 1) (⌈T * Real.log D⌉ + 1) :=
    fun ρ hρ => boxIndex_mem_Icc hχ1 hD hρ
  have hzc : zeroCountM χ σ T = ∑ ρ ∈ boxZeros χ σ 1 T, ((zeroMult χ ρ : ℕ) : ℝ) := rfl
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun ρ => ((zeroMult χ ρ : ℕ) : ℝ))
  exact hzc.trans hfib.symm

/-- The box sits in the disc of centre `1 + (k + ½)Δ·I` and radius `Δ·√(λ² + ¼)`,
`λ = (1 − σ) log D` — no strip binder: `σ ≤ Re ρ ≤ 1` is the box's, `Im ρ ∈ [kΔ, (k+1)Δ)` the
index's. -/
theorem boxFibre_subset_closedBall {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    {σ T D : ℝ} (hD : 1 < D) (k : ℤ) :
    ∀ ρ ∈ boxFibre χ σ T D k,
      ρ ∈ closedBall ((1 : ℂ) + ((((k : ℝ) + 1 / 2) / Real.log D : ℝ) : ℂ) * I)
        (Real.sqrt (((1 - σ) * Real.log D) ^ 2 + 1 / 4) / Real.log D) := by
  intro ρ hρ
  have hmem := Finset.mem_filter.mp hρ
  have hspec := (mem_boxZeros hχ1).mp hmem.1
  have hre : σ ≤ ρ.re := hspec.2.1
  have hre1 : ρ.re ≤ 1 := hspec.2.2.1
  have hL : 0 < Real.log D := Real.log_pos hD
  have hidx : ⌊ρ.im * Real.log D⌋ = k := hmem.2
  have hk1 : ((k : ℤ) : ℝ) ≤ ρ.im * Real.log D := by
    have hfl := Int.floor_le (ρ.im * Real.log D)
    rwa [hidx] at hfl
  have hk2 : ρ.im * Real.log D < ((k : ℤ) : ℝ) + 1 := by
    have hfl := Int.lt_floor_add_one (ρ.im * Real.log D)
    rwa [hidx] at hfl
  have hA : (0 : ℝ) ≤ ((1 - σ) * Real.log D) ^ 2 + 1 / 4 := by positivity
  have hcre : ((1 : ℂ) + ((((k : ℝ) + 1 / 2) / Real.log D : ℝ) : ℂ) * I).re = 1 := by simp
  have hcim : ((1 : ℂ) + ((((k : ℝ) + 1 / 2) / Real.log D : ℝ) : ℂ) * I).im
      = ((k : ℝ) + 1 / 2) / Real.log D := by simp
  have hrhs : Real.sqrt ((((1 - σ) * Real.log D) ^ 2 + 1 / 4) / Real.log D ^ 2)
      = Real.sqrt (((1 - σ) * Real.log D) ^ 2 + 1 / 4) / Real.log D := by
    rw [Real.sqrt_div hA, Real.sqrt_sq hL.le]
  rw [Metric.mem_closedBall, Complex.dist_eq_re_im, hcre, hcim, ← hrhs]
  refine Real.sqrt_le_sqrt ?_
  rw [le_div_iff₀ (pow_pos hL 2)]
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = ρ.im - ((k : ℝ) + 1 / 2) / Real.log D := ⟨_, rfl⟩
  rw [← hv]
  have hLne : Real.log D ≠ 0 := ne_of_gt hL
  have hvL : v * Real.log D = ρ.im * Real.log D - ((k : ℝ) + 1 / 2) := by
    rw [hv, sub_mul, div_mul_cancel₀ _ hLne]
  have hvsq : v ^ 2 * Real.log D ^ 2 = (ρ.im * Real.log D - ((k : ℝ) + 1 / 2)) ^ 2 := by
    rw [← mul_pow, hvL]
  have hbnd : (ρ.im * Real.log D - ((k : ℝ) + 1 / 2)) ^ 2 ≤ 1 / 4 := by nlinarith [hk1, hk2]
  have hu : (ρ.re - 1) ^ 2 ≤ (1 - σ) ^ 2 := by nlinarith [hre, hre1]
  have h1 : (ρ.re - 1) ^ 2 * Real.log D ^ 2 ≤ (1 - σ) ^ 2 * Real.log D ^ 2 :=
    mul_le_mul_of_nonneg_right hu (sq_nonneg _)
  linarith [h1, hvsq, hbnd]

/-- W1 at height on the box's disc, W1's constant THREADED: for any `C₁ > 0` with W1's property
(`hC₁` is the body of `LFunction_zero_count_near_one_at_height`'s `∃ C`, verbatim), the box's count
is `≤ C₁·(7/4 + 3λ/2)` on `D = qT ≥ 10²⁰`, `T ≥ 2`, the strip `119/120 ≤ σ ≤ 1`. The upper edge
is truth-load-bearing: at `σ > 1` the box is EMPTY (the count is `0`) while the bound is NEGATIVE
for `λ < −7/6` (`q = 3`, `T = 10²⁰`, `σ = 2`, `C₁ = 7200`: `−496,623`) — the pass's one kill. -/
theorem efMultTotal_boxFibre_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {σ T : ℝ} (hσ : 119 / 120 ≤ σ) (hσ1 : σ ≤ 1) (hT : 2 ≤ T)
    (hD : 10 ^ 20 ≤ (q : ℝ) * T) {C₁ : ℝ} (hC₁0 : 0 < C₁)
    (hC₁ : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → 2 ≤ q →
      ∀ (t₀ : ℝ) {r : ℝ}, 0 < r → r < 1 / 2 →
        ((∑ᶠ u, MeromorphicOn.divisor (LFunction χ) (closedBall ((1 : ℂ) + (t₀ : ℂ) * I) r) u
            : ℤ) : ℝ)
          ≤ C₁ * (1 + r * Real.log ((q : ℝ) + |t₀| + 2)))
    (k : ℤ) :
    efMultTotal χ (boxFibre χ σ T ((q : ℝ) * T) k)
      ≤ C₁ * (7 / 4 + 3 / 2 * ((1 - σ) * Real.log ((q : ℝ) * T))) := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hD1 : (1 : ℝ) < (q : ℝ) * T := lt_of_lt_of_le (by norm_num) hD
  have hbig : (16 : ℝ) ≤ (q : ℝ) * T := le_trans (by norm_num) hD
  have hL : 0 < Real.log ((q : ℝ) * T) := Real.log_pos hD1
  have hlog46 : (46 : ℝ) ≤ Real.log ((q : ℝ) * T) := by
    have hbase : ((10 : ℝ)) ^ (20 : ℕ) = ((2 : ℝ) * 5) ^ (20 : ℕ) := by norm_num
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h5 : (1.6094379123 : ℝ) < Real.log 5 := Real.log_five_gt_d9
    have hstep : (46 : ℝ) ≤ Real.log ((10 : ℝ) ^ (20 : ℕ)) := by
      rw [hbase, Real.log_pow, Real.log_mul (by norm_num) (by norm_num)]
      push_cast
      linarith
    exact hstep.trans (Real.log_le_log (by positivity) hD)
  have hlam0 : (0 : ℝ) ≤ (1 - σ) * Real.log ((q : ℝ) * T) :=
    mul_nonneg (by linarith) hL.le
  have hlam120 : (1 - σ) * Real.log ((q : ℝ) * T) ≤ Real.log ((q : ℝ) * T) / 120 := by
    have hprod : (0 : ℝ) ≤ (1 / 120 - (1 - σ)) * Real.log ((q : ℝ) * T) :=
      mul_nonneg (by linarith) hL.le
    nlinarith [hprod]
  have hB0 : (0 : ℝ) ≤ C₁ * (7 / 4 + 3 / 2 * ((1 - σ) * Real.log ((q : ℝ) * T))) :=
    mul_nonneg hC₁0.le (by linarith)
  rcases Finset.eq_empty_or_nonempty (boxFibre χ σ T ((q : ℝ) * T) k) with hemp | hne
  · rw [hemp]
    have hz : efMultTotal χ (∅ : Finset ℂ) = 0 := by simp [efMultTotal]
    rw [hz]
    exact hB0
  obtain ⟨ρ₀, hρ₀⟩ := hne
  have hρ₀Z : ρ₀ ∈ boxZeros χ σ 1 T := (Finset.mem_filter.mp hρ₀).1
  have hidx : boxIndex ((q : ℝ) * T) ρ₀ = k := (Finset.mem_filter.mp hρ₀).2
  have hkIcc := boxIndex_mem_Icc hχ1 hD1 hρ₀Z
  rw [hidx] at hkIcc
  obtain ⟨hkl, hkr⟩ := Finset.mem_Icc.mp hkIcc
  have hceil : ((⌈T * Real.log ((q : ℝ) * T)⌉ : ℤ) : ℝ) < T * Real.log ((q : ℝ) * T) + 1 :=
    Int.ceil_lt_add_one _
  have hkR1 : -((⌈T * Real.log ((q : ℝ) * T)⌉ : ℤ) : ℝ) - 1 ≤ ((k : ℤ) : ℝ) := by
    exact_mod_cast hkl
  have hkR2 : ((k : ℤ) : ℝ) ≤ ((⌈T * Real.log ((q : ℝ) * T)⌉ : ℤ) : ℝ) + 1 := by
    exact_mod_cast hkr
  have habs : |((k : ℤ) : ℝ) + 1 / 2| ≤ T * Real.log ((q : ℝ) * T) + 5 / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have ht0 : |(((k : ℤ) : ℝ) + 1 / 2) / Real.log ((q : ℝ) * T)| ≤ T + 1 := by
    rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]
    linarith
  have hrad : Real.sqrt (((1 - σ) * Real.log ((q : ℝ) * T)) ^ 2 + 1 / 4)
      ≤ (1 - σ) * Real.log ((q : ℝ) * T) + 1 / 2 := by
    have h1 : ((1 - σ) * Real.log ((q : ℝ) * T)) ^ 2 + 1 / 4
        ≤ ((1 - σ) * Real.log ((q : ℝ) * T) + 1 / 2) ^ 2 := by nlinarith [hlam0]
    calc Real.sqrt (((1 - σ) * Real.log ((q : ℝ) * T)) ^ 2 + 1 / 4)
        ≤ Real.sqrt (((1 - σ) * Real.log ((q : ℝ) * T) + 1 / 2) ^ 2) := Real.sqrt_le_sqrt h1
      _ = (1 - σ) * Real.log ((q : ℝ) * T) + 1 / 2 := Real.sqrt_sq (by linarith)
  have hr0 : 0 < Real.sqrt (((1 - σ) * Real.log ((q : ℝ) * T)) ^ 2 + 1 / 4)
      / Real.log ((q : ℝ) * T) :=
    div_pos (Real.sqrt_pos.mpr (by positivity)) hL
  have hrhalf : Real.sqrt (((1 - σ) * Real.log ((q : ℝ) * T)) ^ 2 + 1 / 4)
      / Real.log ((q : ℝ) * T) < 1 / 2 := by
    rw [div_lt_iff₀ hL]
    linarith [hrad, hlam120, hlog46]
  have hzero : ∀ ρ ∈ boxFibre χ σ T ((q : ℝ) * T) k, LFunction χ ρ = 0 :=
    fun ρ hρ => ((mem_boxZeros hχ1).mp (Finset.mem_filter.mp hρ).1).1
  have hdiv := efMultTotal_le_divisor hχ1 (isCompact_closedBall _ _)
    (boxFibre_subset_closedBall hχ1 hD1 k) hzero
  have hC := hC₁ χ hχ hq ((((k : ℤ) : ℝ) + 1 / 2) / Real.log ((q : ℝ) * T)) hr0 hrhalf
  refine le_trans hdiv (le_trans hC ?_)
  refine mul_le_mul_of_nonneg_left ?_ hC₁0.le
  have hqT : (q : ℝ) + T + 3 ≤ (q : ℝ) * T := by
    have hmul : (q : ℝ) * T ≤ (2 * ((q : ℝ) - 1)) * (2 * (T - 1)) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  have hlogle : Real.log ((q : ℝ)
        + |(((k : ℤ) : ℝ) + 1 / 2) / Real.log ((q : ℝ) * T)| + 2)
      ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log (by positivity) (by linarith)
  have hstep := mul_le_mul_of_nonneg_left hlogle hr0.le
  have hrL : Real.sqrt (((1 - σ) * Real.log ((q : ℝ) * T)) ^ 2 + 1 / 4)
        / Real.log ((q : ℝ) * T) * Real.log ((q : ℝ) * T)
      = Real.sqrt (((1 - σ) * Real.log ((q : ℝ) * T)) ^ 2 + 1 / 4) :=
    div_mul_cancel₀ _ hL.ne'
  rw [hrL] at hstep
  linarith [hstep, hrad, hlam0]

/-- The representatives of the boxes of ONE parity `c ∈ {0, 1}` are `Δ`-well-spaced: boxes
`k ≠ k'` with `k % 2 = k' % 2` have `|k − k'| ≥ 2`, so the gap is strictly
`> (|k − k'| − 1)Δ ≥ Δ`. -/
theorem wellSpacedAt_parity_reps {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {σ T D : ℝ}
    (hD : 1 < D) (c : ℤ) :
    WellSpacedAt (1 / Real.log D)
      (((Finset.Icc (-⌈T * Real.log D⌉ - 1) (⌈T * Real.log D⌉ + 1)).filter
          (fun k => k % 2 = c ∧ (boxFibre χ σ T D k).Nonempty)).image
        (fun k => (boxRep χ σ T D k).im)) := by
  have hL : 0 < Real.log D := Real.log_pos hD
  have hb : ∀ j : ℤ, (boxFibre χ σ T D j).Nonempty →
      ((j : ℤ) : ℝ) ≤ (boxRep χ σ T D j).im * Real.log D ∧
        (boxRep χ σ T D j).im * Real.log D < ((j : ℤ) : ℝ) + 1 := by
    intro j hj
    have hmem := boxRep_mem hj
    have hidx : ⌊(boxRep χ σ T D j).im * Real.log D⌋ = j := (Finset.mem_filter.mp hmem).2
    have h1 := Int.floor_le ((boxRep χ σ T D j).im * Real.log D)
    have h2 := Int.lt_floor_add_one ((boxRep χ σ T D j).im * Real.log D)
    rw [hidx] at h1 h2
    exact ⟨h1, h2⟩
  intro t ht r hr hne
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hr
  have hkf := Finset.mem_filter.mp hk
  have hk'f := Finset.mem_filter.mp hk'
  have hkne : k ≠ k' := fun hkk => hne (by rw [hkk])
  obtain ⟨ha1, ha2⟩ := hb k hkf.2.2
  obtain ⟨hb1, hb2⟩ := hb k' hk'f.2.2
  have hpar : k % 2 = k' % 2 := by rw [hkf.2.1, hk'f.2.1]
  have hgap2 : k + 2 ≤ k' ∨ k' + 2 ≤ k := by omega
  rcases hgap2 with hle | hle
  · have hc : ((k : ℤ) : ℝ) + 2 ≤ ((k' : ℤ) : ℝ) := by exact_mod_cast hle
    have hab : (boxRep χ σ T D k).im < (boxRep χ σ T D k').im :=
      lt_of_mul_lt_mul_right (by linarith) hL.le
    have hnp : (boxRep χ σ T D k).im - (boxRep χ σ T D k').im ≤ 0 := by linarith
    rw [abs_of_nonpos hnp, neg_sub, div_le_iff₀ hL]
    linarith
  · have hc : ((k' : ℤ) : ℝ) + 2 ≤ ((k : ℤ) : ℝ) := by exact_mod_cast hle
    have hab : (boxRep χ σ T D k').im < (boxRep χ σ T D k).im :=
      lt_of_mul_lt_mul_right (by linarith) hL.le
    have hnn : (0 : ℝ) ≤ (boxRep χ σ T D k).im - (boxRep χ σ T D k').im := by linarith
    rw [abs_of_nonneg hnn, div_le_iff₀ hL]
    linarith

/-- The count is at most the box bound times the number of NON-EMPTY boxes — the even ones plus
the odd ones, each cardinal spelled as its filtered Finset's `.card` (every `k` has
`k % 2 ∈ {0, 1}`); `σ ≤ 1` as on the per-box row (its route invokes that row at every `k`). -/
theorem zeroCountM_le_box_bound_mul {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {σ T : ℝ} (hσ : 119 / 120 ≤ σ) (hσ1 : σ ≤ 1) (hT : 2 ≤ T)
    (hD : 10 ^ 20 ≤ (q : ℝ) * T) {C₁ : ℝ} (hC₁0 : 0 < C₁)
    (hC₁ : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → 2 ≤ q →
      ∀ (t₀ : ℝ) {r : ℝ}, 0 < r → r < 1 / 2 →
        ((∑ᶠ u, MeromorphicOn.divisor (LFunction χ) (closedBall ((1 : ℂ) + (t₀ : ℂ) * I) r) u
            : ℤ) : ℝ)
          ≤ C₁ * (1 + r * Real.log ((q : ℝ) + |t₀| + 2))) :
    zeroCountM χ σ T
      ≤ C₁ * (7 / 4 + 3 / 2 * ((1 - σ) * Real.log ((q : ℝ) * T)))
        * (((Finset.Icc (-⌈T * Real.log ((q : ℝ) * T)⌉ - 1)
                  (⌈T * Real.log ((q : ℝ) * T)⌉ + 1)).filter
                (fun k => k % 2 = 0 ∧ (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty)).card
            + ((Finset.Icc (-⌈T * Real.log ((q : ℝ) * T)⌉ - 1)
                  (⌈T * Real.log ((q : ℝ) * T)⌉ + 1)).filter
                (fun k => k % 2 = 1 ∧ (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty)).card : ℕ) := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hD1 : (1 : ℝ) < (q : ℝ) * T := lt_of_lt_of_le (by norm_num) hD
  have hL : 0 < Real.log ((q : ℝ) * T) := Real.log_pos hD1
  have hlam0 : (0 : ℝ) ≤ (1 - σ) * Real.log ((q : ℝ) * T) :=
    mul_nonneg (by linarith) hL.le
  have hB0 : (0 : ℝ) ≤ C₁ * (7 / 4 + 3 / 2 * ((1 - σ) * Real.log ((q : ℝ) * T))) :=
    mul_nonneg hC₁0.le (by linarith)
  rw [zeroCountM_eq_sum_boxFibre hχ1 hD1]
  set I := Finset.Icc (-⌈T * Real.log ((q : ℝ) * T)⌉ - 1) (⌈T * Real.log ((q : ℝ) * T)⌉ + 1)
  have hzeroes : ∑ k ∈ I.filter (fun k => ¬ (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty),
      efMultTotal χ (boxFibre χ σ T ((q : ℝ) * T) k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.not_nonempty_iff_eq_empty.mp (Finset.mem_filter.mp hk).2]
    simp [efMultTotal]
  have hsplit : ∑ k ∈ I, efMultTotal χ (boxFibre χ σ T ((q : ℝ) * T) k)
      = ∑ k ∈ I.filter (fun k => (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty),
          efMultTotal χ (boxFibre χ σ T ((q : ℝ) * T) k) := by
    rw [← Finset.sum_filter_add_sum_filter_not I
      (fun k => (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty), hzeroes, add_zero]
  have hP : ∀ k ∈ I.filter (fun k => (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty),
      efMultTotal χ (boxFibre χ σ T ((q : ℝ) * T) k)
        ≤ C₁ * (7 / 4 + 3 / 2 * ((1 - σ) * Real.log ((q : ℝ) * T))) :=
    fun k _ => efMultTotal_boxFibre_le hχ hq hσ hσ1 hT hD hC₁0 hC₁ k
  have hsub : I.filter (fun k => (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty)
      ⊆ I.filter (fun k => k % 2 = 0 ∧ (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty)
        ∪ I.filter (fun k => k % 2 = 1 ∧ (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty) := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk'.1, h0, hk'.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk'.1, h1, hk'.2⟩)
  have hcard : (I.filter (fun k => (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty)).card
      ≤ (I.filter (fun k => k % 2 = 0 ∧ (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty)).card
        + (I.filter (fun k => k % 2 = 1 ∧ (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty)).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  rw [hsplit]
  calc ∑ k ∈ I.filter (fun k => (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty),
        efMultTotal χ (boxFibre χ σ T ((q : ℝ) * T) k)
      ≤ (I.filter (fun k => (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty)).card
          • (C₁ * (7 / 4 + 3 / 2 * ((1 - σ) * Real.log ((q : ℝ) * T)))) :=
        Finset.sum_le_card_nsmul _ _ _ hP
    _ = C₁ * (7 / 4 + 3 / 2 * ((1 - σ) * Real.log ((q : ℝ) * T)))
          * ((I.filter (fun k => (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty)).card : ℝ) := by
        rw [nsmul_eq_mul]; ring
    _ ≤ C₁ * (7 / 4 + 3 / 2 * ((1 - σ) * Real.log ((q : ℝ) * T)))
          * (((I.filter (fun k => k % 2 = 0 ∧ (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty)).card
              + (I.filter
                  (fun k => k % 2 = 1 ∧ (boxFibre χ σ T ((q : ℝ) * T) k).Nonempty)).card
                : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hB0

/-- **The shape control** (the design v2's A5, third limb): `7/4 + 3λ/2 ≤ (7/4)·e^{λ}` at `λ = 0`
(equality; at `λ = 1`: `3.25 ≤ 4.76`, a docstring receipt) — the box factor is `≤ (7/4)e^{λ}`,
F6's fourth free class. -/
example : (7 : ℝ) / 4 + 3 / 2 * 0 ≤ 7 / 4 * Real.exp 0 := by simp

/-- **The W9e exit row**: the box index at a numeral — `Im ρ = 3`, `D = e`, so `k = ⌊3⌋ = 3`
(INVOKING the frozen def; `Real.log_exp`). -/
example : boxIndex (Real.exp 1) (2 + (3 : ℝ) * I) = 3 := by
  simp [boxIndex]

end Salt.SW
