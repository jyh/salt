/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.DensityCrude

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

end Salt.SW
