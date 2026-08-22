/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# Block C — the λ-quality supply for MRT Theorem A.1

MRT's Theorem A.1 is quantified by the quality `M(f; X)` of (1.6) (p. 4):

  `M(g; X) := inf_{|t| ≤ X} 𝔻(g, n^{it}; X)²`   (`Salt.MR.mrtM`)

and the campaign needs a LOWER bound on `M(λ; X)`, because A.1's conclusion is
governed by `exp(−M)·M` — larger `M` is a stronger conclusion, so a lower bound
on the quality is what the hypothesis slot consumes.

That supply is already landed: `Salt.MR.lambda_nonpret` (`NonPretClose.lean:49`)
is unconditional and effective, and holds for every `|t| ≤ Q·x`.  This file does
the one thing that was missing — turning the per-`t` bound into a bound on the
INFIMUM, which is what `mrtM` actually is.

## The `t`-uniformity step, which is the whole content

`lambda_nonpret`'s bound carries the honest correction term
`−4·logloglog(|t| + 16)`, which DEPENDS ON `t`.  An infimum over `|t| ≤ X` must
therefore be taken against the worst admissible `t`, and since the correction
enters with a NEGATIVE coefficient the worst case is the LARGEST `|t|`, i.e.
`|t| = X`.  `log3_shift_mono` supplies exactly that monotonicity, and the
resulting bound

  `M(λ; X) ≥ (1/4)·loglog X − 4·logloglog(X + 16) − C`

is `(1/4 − o(1))·loglog X`, since `logloglog = o(loglog)`.

⚠️ The `+ 16` shift is not cosmetic: it is what keeps the triple logarithm in the
range where it is defined and monotone (`a + 16 ≥ 16 > e`, so `log(a+16) > 1`
and `loglog(a+16) > 0`).  The monotonicity lemma is stated with that shift baked
in for precisely this reason.

## Why this file exists rather than an edit to `MRTProp24.lean`

`MRTProp24.lean` is a STATEMENT module — wave 1a's `MRTProp24Statement` is a
`Prop` that nothing proves and nothing assumes.  Keeping the supply wiring out
of it preserves that property.
-/
import Mathlib
import Salt.MR.MRTProp24
import Salt.MR.NonPretClose

namespace Salt.MR

open scoped BigOperators

/-- **Monotonicity of the shifted triple logarithm.**  For `0 ≤ a ≤ b`,
`logloglog(a + 16) ≤ logloglog(b + 16)`.  The `+ 16` keeps every intermediate
value in the domain where `Real.log` is monotone: `a + 16 ≥ 16 > e` gives
`log(a + 16) > 1`, hence `loglog(a + 16) > 0`. -/
theorem log3_shift_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.log (Real.log (Real.log (a + 16)))
      ≤ Real.log (Real.log (Real.log (b + 16))) := by
  have hpos1 : (0 : ℝ) < a + 16 := by linarith
  have hle1 : a + 16 ≤ b + 16 := by linarith
  have hL1 : Real.log (a + 16) ≤ Real.log (b + 16) := Real.log_le_log hpos1 hle1
  have hlog16 : (1 : ℝ) < Real.log (a + 16) := by
    rw [Real.lt_log_iff_exp_lt hpos1]
    have := Real.exp_one_lt_d9
    linarith
  have hpos2 : (0 : ℝ) < Real.log (a + 16) := by linarith
  have hL2 : Real.log (Real.log (a + 16)) ≤ Real.log (Real.log (b + 16)) :=
    Real.log_le_log hpos2 hL1
  exact Real.log_le_log (Real.log_pos hlog16) hL2

/-- **BLOCK C — the λ-quality lower bound in the shape `M(λ; X)` consumes.**
`M(λ; X) ≥ (1/4)·loglog X − 4·logloglog(X + 16) − C` for all large `X`,
unconditional and effective, obtained from `lambda_nonpret` at `Q = 1` by taking
the infimum against the worst admissible twist `|t| = X`. -/
theorem mrtM_lam_lower :
    ∃ x0 C : ℝ, ∀ X : ℝ, x0 ≤ X →
      (1 / 4) * Real.log (Real.log X)
          - 4 * Real.log (Real.log (Real.log (X + 16))) - C
        ≤ mrtM lam X := by
  obtain ⟨x0, C, h⟩ := lambda_nonpret 1 le_rfl
  refine ⟨max x0 16, C, ?_⟩
  intro X hX
  have hx0 : x0 ≤ X := le_trans (le_max_left _ _) hX
  have h16 : (16 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : (0 : ℝ) ≤ X := by linarith
  unfold mrtM
  apply le_csInf
  · exact ⟨pretDistSq lam (costwist 0) X, 0, by simpa using hX0, rfl⟩
  · rintro b ⟨t, htX, rfl⟩
    have hb := h X t hx0 (by rwa [one_mul])
    have hmono := log3_shift_mono (abs_nonneg t) htX
    linarith

end Salt.MR
