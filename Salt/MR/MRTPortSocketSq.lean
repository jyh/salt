/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Close

/-!
# The split socket, re-served with an `L²` open binder (`MRTPortSocketSq`)

`M4Exit.m4_exit_socket_split` (`M4Exit.lean:487`) exposes ONE open binder: an `L¹`
door bound `∫‖absWindowSum lamCoeff H · α‖ dμ ≤ δ₀·H`, uniform over the window range
`[R.Hlo, R.Hhi]` and over the near-rational frequencies `α`.  The MRT port's supply
side is a MEAN SQUARE, not a mean: Theorem A.1 prices `(1/X)∫‖shortMean‖²`, and every
link of the door composition beneath it (`m4_bridge_door_sq_le`, `M4RowMeanSq`) is
stated in `L²`.

This file re-serves the socket so its open binder is the `L²` demand at grade
`δ₀²·H²`.  Nothing analytic is added: the `L²→L¹` step is the landed
`M4Close.integral_logMeasure_le_sqrt_of_sq` (`M4Close.lean:191`), which carries no
integrability side condition, and the only arithmetic is `√(δ₀²H²) = δ₀·H` under two
nonnegativity facts the `ChowlaRegime` record already holds (`R.hx`, `R.hω`).

The `∃`-prefix, the `∀ (U1floor) (g)` lever and the full conjunct list — including the
TOWER conjunct, which is forwarded unused exactly as the split socket forwards it — are
reproduced verbatim from the landed socket; only the door integral changes.
-/

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **The δ₀ split socket, `L²`-served.**  Identical to `m4_exit_socket_split` except
that the one open binder is the SQUARED door demand `∫‖·‖² dμ ≤ δ₀²·H²`, which is the
shape MRT Theorem A.1 and the door's row descent actually produce.  Cauchy–Schwarz
against the log measure (`integral_logMeasure_le_sqrt_of_sq`) discharges the socket's
own `L¹` binder from it. -/
theorem m4_exit_socket_split_of_sq :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ 5) ∧
          ((∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
              NearRatTight (arcDen 12 H) H α →
                (∫ n, ‖absWindowSum lamCoeff H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                  ≤ δ₀ ^ 2 * (H : ℝ) ^ 2) →
            ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨ε, δ₀, hε, hδ₀, hsock⟩ := m4_exit_socket_split
  refine ⟨ε, δ₀, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hR⟩ := hsock U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, fun hsq => hR ?_⟩
  intro H hH hlo hhi α harc
  haveI : NeZero H := hH
  have hsqrt : Real.sqrt (δ₀ ^ 2 * (H : ℝ) ^ 2) = δ₀ * (H : ℝ) := by
    rw [Real.sqrt_mul (sq_nonneg δ₀), Real.sqrt_sq hδ₀.le,
      Real.sqrt_sq (Nat.cast_nonneg H)]
  have hB := integral_logMeasure_le_sqrt_of_sq R.hx R.hω
    (f := fun n => ‖absWindowSum lamCoeff H n α‖) (fun _ => norm_nonneg _)
    (hsq H hlo hhi α harc)
  rwa [hsqrt] at hB

end Salt.MR
