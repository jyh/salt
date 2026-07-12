/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# T2 — the log-weight integral

Design: `docs/blueprints/twinbar.md`, node `T2` and proof-chain step (i).
This is the per-slice normalization constant feeding the twin-bar rung's
Cauchy–Schwarz step (T3): for `a > 0`,

  `∫ t in 0..a, (a + t)⁻¹ = log 2`,

obtained by shifting the integration variable (`t ↦ a + t`, landing the
range `a..2a`) and then applying mathlib's closed form for `∫ x⁻¹` on an
interval avoiding `0`, collapsing `log (2a / a)` to `log 2`. The two
companion facts recorded here (`logWeight_inv_nonneg`, `logWeight_inv_le`)
are exactly what T3's Cauchy–Schwarz slice argument needs about the same
integrand `(a + t)⁻¹` on the slice `t ≥ 0`.

Standalone module: imports only `Mathlib`, no dependency on
`Salt/TwinBar/Defs.lean` (owned by a concurrent node on the carriers).
-/

namespace Salt.TwinBar

open intervalIntegral

/-- T2: the per-slice log-weight integral. The shift `t ↦ a + t`
(`intervalIntegral.integral_comp_add_left`) turns the range `0..a` into
`a..a+a`; `integral_inv_of_pos` gives `log ((a+a)/a)`, which collapses to
`log 2` since `a ≠ 0`. -/
theorem logWeight {a : ℝ} (ha : 0 < a) :
    ∫ t in (0:ℝ)..a, (a + t)⁻¹ = Real.log 2 := by
  have hshift : (∫ t in (0:ℝ)..a, (fun x : ℝ => x⁻¹) (a + t))
      = ∫ x in a + 0..a + a, (fun x : ℝ => x⁻¹) x :=
    intervalIntegral.integral_comp_add_left (fun x : ℝ => x⁻¹) a
  simp only [add_zero] at hshift
  rw [hshift]
  have h2a : a + a = 2 * a := by ring
  rw [h2a, integral_inv_of_pos ha (by linarith), mul_div_assoc, div_self ha.ne', mul_one]

/-- Companion for T3: the integrand `(a + t)⁻¹` is nonnegative on the
slice `t ≥ 0` (for `a > 0`). -/
lemma logWeight_inv_nonneg {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) : 0 ≤ (a + t)⁻¹ := by
  positivity

/-- Companion for T3: the reciprocal bound `(a + t)⁻¹ ≤ a⁻¹` for `t ≥ 0`. -/
lemma logWeight_inv_le {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) : (a + t)⁻¹ ≤ a⁻¹ := by
  gcongr
  linarith

end Salt.TwinBar
