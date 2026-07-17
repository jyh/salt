/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The decoupling combine (Tao 1509.05422 §3, toward (3.15)/(3.16)), spine nodes W3-a-1/2

The y-side decoupling of the F-function bridge.  Tao's step from (3.14) toward
(3.15) replaces the random residue input `y` by its mean: at the Liouville model
instantiation (`a = 1, b = 0, h = 1, c_p = 1`), the `y`-average of `F(x, ·)`
is exactly the decoupled two-point correlation `∑_{p ∈ 𝒫_H} (1/p) ∑_j v_j v_{j+p}`
(node W3-a-1, `fBridgeF_mean`), and Hoeffding concentration transports the
(3.14) concentration statement onto that decoupled diagonal (node W3-a-2,
`fBridge_concentration_decoupled`).

Both statements were frozen and validity-probed by the A3-W3R recon
(2026-07-19): proven end-to-end from the landed wave-1/2 API, with the
degenerate zero-window instance checked separately.

The OUTER combine — from the Chowla-failure hypothesis (2.11) through the
good-`x` selector to (3.16) — is deliberately NOT here: it needs new doors
(the (2.11) input, outer `logMeasure` expectation plumbing) and is deferred to
a house design block (`docs/exploration/s3-a3-design.md`, node W3-a-3).
-/
import Salt.Entropy.Chowla.FBridge
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

variable (eps : ℚ) (H : ℕ)

/-- **W3-a-1, the decoupled y-mean** (the model form of Tao's (3.14) → (3.15)
identity `(1/P_H) ∑_y F(x, y) = ∑_{p ∈ 𝒫_H} (1/p) ∑_j x_j x_{j+p}`).  The
`y`-average of the F-bridge is the decoupled two-point correlation: linearity
of the integral over the per-prime components plus `fBridgeG_mean`. -/
theorem fBridgeF_mean (v : Fin H → ℤ) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω => fBridgeF eps H v ω]
      = ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ) := by
  classical
  have hpt : (fun ω => fBridgeF eps H v ω)
      = fun ω => ∑ p : primeWindow eps H, fBridgeG eps H v p (residueProj eps H p ω) := rfl
  rw [hpt, integral_finsetSum Finset.univ (fun p _ => Integrable.of_finite)]
  exact Finset.sum_congr rfl (fun p _ => fBridgeG_mean eps H p)

/-- **W3-a-2, concentration on the decoupled diagonal** (the Lemma 3.3 output
with the `y`-mean replaced via `fBridgeF_mean`): for a `‖·‖ ≤ 1` window
pattern, `F` deviates from the decoupled two-point correlation by `≥ δ` with
probability `≤ 2 exp(−δ² / (2(ε²H + 1)(2/ε² + 1)²))`.  Substitution of the
decoupled mean into `fBridge_concentration`. -/
theorem fBridge_concentration_decoupled
    {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (heps : 0 < eps)
    (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF eps H v ω - ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
            ∑ j ∈ Finset.range H,
              (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ)|}
      ≤ 2 * Real.exp (-δ ^ 2 /
          (2 * (((eps : ℝ) ^ 2 * (H : ℝ) + 1) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2))) := by
  have hmean : (∑ p : primeWindow eps H,
        (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
          fBridgeG eps H v p (residueProj eps H p ω)])
      = ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ) :=
    Finset.sum_congr rfl (fun p _ => fBridgeG_mean eps H p)
  have h := fBridge_concentration eps H hv heps hne hδ
  rw [hmean] at h
  exact h

end Salt.Entropy.Chowla
