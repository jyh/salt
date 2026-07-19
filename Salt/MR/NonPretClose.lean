/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.NonPret
import Salt.MR.PrimeTail

/-!
# S8 MR-CORE wave-2 rung R1.3 — the UNCONDITIONAL λ-non-pretentiousness (`lambda_nonpret`)

This file CLOSES the campaign's oldest open hypothesis: the Euler bridge residual of
`Salt/MR/NonPret.lean`.  The landed `lambda_nonpret_of_bridge` (NonPret.lean:114) took the
λ-Euler bridge `𝔻² ≥ loglog x + log‖ζ(1+1/logx+it)‖ − K` as a *named hypothesis*; the H0
wave discharged that bridge UNCONDITIONALLY (`euler_osc_bridge_unconditional`,
`Salt/MR/PrimeTail.lean`, via the R0.2 dyadic tail).  Here we compose the two to obtain the
S5 range/quality SPLIT bound with NO remaining hypothesis.

## The glue (freeze R1.3, ~40 ln)

The bridge hypothesis of `lambda_nonpret_of_bridge` is exactly
`loglog x + log‖ζ(1+1/logx+it)‖ − K ≤ 𝔻(λ, n^{it}; x)²`.  We discharge it from:

* `pretDistSq_liouville_split` + `costwist_re` : `𝔻(λ, n^{it}; x)²`
  `= SPartial x + ∑_{p≤x} cos(t·log p)/p` (the divergent Mertens part plus the oscillation part);
* `euler_osc_bridge_unconditional` : `|∑_{p≤x} cos(t·log p)/p − log‖ζ‖| ≤ K`, so the oscillation
  part is `≥ log‖ζ‖ − K` (the λ-side `≥` corollary);
* `mertens_second_sharp_real` : `SPartial x ≥ loglog x + M − 12/log x` — the sharp REAL Mertens-2,
  which already compares against `loglog x` (real `x`, not `loglog ⌊x⌋`), so the floor-gap is
  absorbed; and `12/log x ≤ 12` for `x ≥ e`.

Composing: `𝔻² ≥ loglog x + log‖ζ‖ + (M − 12 − K)`, so the bridge holds with the constant
`12 + K − M`.  `lambda_nonpret` then follows by `lambda_nonpret_of_bridge`.
-/

namespace Salt.MR

open scoped BigOperators

/-- **R1.3 — the UNCONDITIONAL λ-non-pretentiousness (`lambda_nonpret`).**  The S5 range/quality
SPLIT bound with NO remaining hypothesis (the Euler bridge residual is discharged by the H0 wave).
For every `Q ≥ 1` there are `x₀, C` with, for all `x ≥ x₀` and `|t| ≤ Q·x`,

  `(1/4)·loglog x − 4·logloglog(|t|+16) − C ≤ 𝔻(λ, n^{it}; x)²`.

This CLOSES the campaign's oldest open hypothesis (the S5 zeta-shadow / Euler-oscillation
bridge).  Coefficient EXACTLY `1/4`; the `−4·logloglog(|t|+16)` correction is the honest
`o(loglog x)` shape (S5 law: never absorbed into `C`). -/
theorem lambda_nonpret :
    ∀ Q : ℝ, 1 ≤ Q → ∃ x0 C : ℝ, ∀ x t : ℝ, x0 ≤ x → |t| ≤ Q * x →
      (1 / 4) * Real.log (Real.log x)
          - 4 * Real.log (Real.log (Real.log (|t| + 16))) - C
        ≤ pretDistSq lam (costwist t) x := by
  obtain ⟨K, hK⟩ := euler_osc_bridge_unconditional
  refine lambda_nonpret_of_bridge (K := 12 + K - Salt.Mertens.mertensM) ?_
  intro x t hx
  -- basic scale facts (`x ≥ e ≥ 2`, `log x ≥ 1`)
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hx2 : (2 : ℝ) ≤ x := le_trans h2e hx
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  -- the λ-side `≥` corollary from the UNCONDITIONAL Euler bridge
  have hbr := hK x t hx
  rw [abs_le] at hbr
  -- the sharp real Mertens lower bound (compares against `loglog x`, floor-gap absorbed)
  have hmert := Salt.Mertens.mertens_second_sharp_real hx2
  rw [abs_le] at hmert
  -- `12/log x ≤ 12` for `x ≥ e`
  have h12 : 12 / Real.log x ≤ 12 := by rw [div_le_iff₀ hLpos]; nlinarith [hlogx1]
  -- `𝔻(λ, n^{it}; x)² = SPartial x + ∑_{p≤x} cos(t·log p)/p`
  have hsplit : pretDistSq lam (costwist t) x
      = Salt.Mertens.SPartial x
        + ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
            Real.cos (t * Real.log p) / (p : ℝ) := by
    rw [pretDistSq_liouville_split lam (costwist t) x (fun p _ => rfl),
        show Salt.Mertens.SPartial x
            = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) from rfl,
        ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [costwist_re]; ring
  rw [hsplit]
  linarith [hbr.1, hbr.2, hmert.1, hmert.2, h12]

end Salt.MR
