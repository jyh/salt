/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.GIntegrals

/-!
# N6.2 — the ratio prize (blueprint N6.2)

Pure one-dimensional calculus.  With the N6.1 closed forms substituted
(`I_g = log(1+A·T)/A`, `J_g = T/(1+A·T)`), and the Maynard scaling
`A = log k`, `T = k^{1/8}/log k`, the variational ratio `I_g²/J_g` grows
like `(log k)/64`.  This is the growth that drives the downstream
"ratio → ∞" needed by N7.1.

The whole computation collapses under the substitution `X := k^{1/8}`, so
that `A·T = X` and `log X = (1/8)·log k = A/8`.  Then
`I_g²/J_g = (log(1+X))²·(1+X)/(A·X)`, and since `log(1+X) ≥ log X = A/8`
and `(1+X)/X ≥ 1`, this is `≥ (A/8)²/A = A/64 = (log k)/64`.
-/

namespace Salt.Maynard

/-- Abstract core of the ratio inequality.  For any `A > 0` and `X ≥ 1`
with `log X = A/8`, the closed-form ratio `(log(1+X)/A)² / ((X/A)/(1+X))`
is at least `A/64`.  The Maynard instance takes `A = log k`, `X = k^{1/8}`. -/
private theorem ratio_aux {A X : ℝ} (hA : 0 < A) (hX1 : 1 ≤ X)
    (hlogX : Real.log X = A / 8) :
    (Real.log (1 + X) / A) ^ 2 / ((X / A) / (1 + X)) ≥ A / 64 := by
  have hXpos : 0 < X := lt_of_lt_of_le one_pos hX1
  have h1X : 0 < 1 + X := by linarith
  have hAne : A ≠ 0 := ne_of_gt hA
  have hXne : X ≠ 0 := ne_of_gt hXpos
  have h1Xne : (1 + X) ≠ 0 := ne_of_gt h1X
  set L := Real.log (1 + X) with hLdef
  -- `log(1+X) ≥ log X = A/8`.
  have hLge : A / 8 ≤ L := by
    rw [hLdef, ← hlogX]
    exact Real.log_le_log hXpos (by linarith)
  have hLnn : 0 ≤ L := le_trans (by linarith) hLge
  -- Collapse the compound fraction.
  have hExpr : (L / A) ^ 2 / ((X / A) / (1 + X)) = L ^ 2 * (1 + X) / (A * X) := by
    field_simp
  rw [ge_iff_le, hExpr, div_le_div_iff₀ (by norm_num) (by positivity)]
  -- Reduced goal: `A * (A * X) ≤ L² * (1 + X) * 64`.
  have hLsq : A ^ 2 / 64 ≤ L ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ L - A / 8)
      (by linarith : (0:ℝ) ≤ L + A / 8)]
  have hmX : (0:ℝ) ≤ (L ^ 2 - A ^ 2 / 64) * (1 + X) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hmX, sq_nonneg A, mul_pos hA hXpos]

/-- **N6.2 — the ratio prize.**  With `g(u) = 1/(1 + A·u)`, `A = log k`,
`T = k^{1/8}/log k`, the Maynard variational ratio `I_g²/J_g` grows like
`(log k)/64`; in particular it exceeds any fixed threshold for `k` large.
Here `I_g = log(1+A·T)/A` and `J_g = T/(1+A·T)` are the N6.1 closed forms
(`integral_g`, `integral_g_sq`) substituted. -/
theorem ratio_prize :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      let A := Real.log k
      let T := (k : ℝ) ^ (1/8 : ℝ) / Real.log k
      (Real.log (1 + A * T) / A) ^ 2 / (T / (1 + A * T)) ≥ Real.log k / 64 := by
  refine ⟨2, fun k hk => ?_⟩
  intro A T
  have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hk1 : (1:ℝ) < (k:ℝ) := by linarith
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  have hA : 0 < A := Real.log_pos hk1
  have hAne : A ≠ 0 := ne_of_gt hA
  have hX1 : (1:ℝ) ≤ (k:ℝ) ^ (1/8:ℝ) := Real.one_le_rpow (le_of_lt hk1) (by norm_num)
  have hlogX : Real.log ((k:ℝ) ^ (1/8:ℝ)) = A / 8 := by
    rw [Real.log_rpow hkpos]
    change (1/8:ℝ) * Real.log k = Real.log k / 8
    ring
  have hTeq : T = (k:ℝ) ^ (1/8:ℝ) / A := rfl
  have hAT : A * T = (k:ℝ) ^ (1/8:ℝ) := by
    rw [hTeq]; field_simp
  rw [hAT, hTeq]
  exact ratio_aux hA hX1 hlogX

end Salt.Maynard
