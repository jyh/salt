/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S11ExitL2

/-!
# The TRIVIAL split of the road-form `L²` socket

`S11ExitL2.m4_exit_socket_split_sq_arc` quantifies over an ARBITRARY split
`λ = a + e` (`a` the sieved leg, `e` the insert complement).  This file records
what that generality buys at the degenerate choice

```
a := lamCoeff,   e := 0,   Bsieve := fun _ => δ₀/(2K),   Binsert := 0
```

Three of the socket's four supply legs collapse:

* `hsplit` is `λ m = λ m + 0` — `add_zero`;
* `hins` is the Ξ-summed insert budget at `e = 0`; every `absWindowSum 0 …`
  is a sum of `0 * exp …`, so the integrand, the integral and the Ξ-sum are all
  `0`, and `Binsert := 0` discharges it at `0 ≤ 0`;
* `hρ` is `K·(2·Bsieve H) + 2·0 ≤ δ₀`, which closes AT EQUALITY at
  `Bsieve := δ₀/(2K)` (this is where `0 < K` is spent).

What is left is ONE hypothesis: an UNSIEVED `L²` door bound on `lamCoeff` at a
fixed constant grade `c`.  That is exactly A.1's own object, modulo the phase.

⚠️ This closes a named residual on the δ₀-split road.  It does NOT compose to
the door: the frequency `α` is still present (GAP α, the major arc, class D),
and `MRTThmA1` itself has no producer (class D).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **The road-form split socket at the TRIVIAL split.**  Firing
`m4_exit_socket_split_sq_arc` at `a := lamCoeff`, `e := 0` reduces its four
supply legs to one: an unsieved `L²` door bound at a fixed constant `c`. -/
theorem m4_exit_socket_split_sq_trivial :
    ∃ (ε : ℚ) (c : ℝ), 0 < ε ∧ 0 < c ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          ((∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
              NearRatTight (arcDen 12 H) H α →
                (∫ n, ‖absWindowSum lamCoeff H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                  ≤ c * (H : ℝ) ^ 2) →
            ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨ε, K, δ₀, hε, hK, hδ₀, hsock⟩ := m4_exit_socket_split_sq_arc
  have hc : 0 < δ₀ / (2 * K) := div_pos hδ₀ (by linarith)
  refine ⟨ε, δ₀ / (2 * K), hε, hc, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hRU1, hRg, hRtow, hR⟩ := hsock U1floor g
  refine ⟨R, hReps, hRU1, hRg, hRtow, ?_⟩
  intro hdoor
  refine hR lamCoeff 0 (fun _ => δ₀ / (2 * K)) 0 (fun m => by simp)
    (fun _ => hc.le) hdoor ?_ ?_
  · intro H _ hlo hhi
    have hz : ∀ (n : ℕ) (α : ℝ), absWindowSum (0 : ℕ → ℂ) H n α = 0 := by
      intro n α
      unfold absWindowSum
      simp
    simp [hz]
  · intro H _ _
    have hK' : (2 : ℝ) * K ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < 2 * K)
    field_simp
    linarith

end Salt.MR

end
