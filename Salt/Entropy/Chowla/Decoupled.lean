/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The decoupling combine (Tao arXiv:1509.05422v1 §3, toward (3.15)/(3.16)), spine nodes W3-a-1/2

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

/-! ## The decoupling combine at shift `h` (W-F3 wave B, nodes B-2/B-3)

The `h`-ports of the two statements above, against wave A's `fBridgeF_h`.  ⚠️ Both are SITE 2
of the three synchronised offset spellings (site 1 is `badSet_h`, site 3 is `outer_combine`'s
own conclusion, still unported): the shifted two-point correlation is written with wave A's
fixed spelling `windowVal H v (j + (p : ℕ) * h)`. -/

/-- **The decoupled y-mean at shift `h`** (the `h`-port of `fBridgeF_mean`).  The `y`-average
of the shift-`h` F-bridge is the shifted decoupled two-point correlation
`∑_{p ∈ 𝒫_H} (1/p) ∑_j v_j v_{j+p·h}`: linearity of the integral over the per-prime
components plus `fBridgeG_h_mean`.  The `h = 1` original is recovered by
`fBridgeF_h_one` + `Nat.mul_one` (both rewrites load-bearing; measured). -/
theorem fBridgeF_h_mean (h : ℕ) (v : Fin H → ℤ) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω => fBridgeF_h eps H h v ω]
      = ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) := by
  classical
  have hpt : (fun ω => fBridgeF_h eps H h v ω)
      = fun ω => ∑ p : primeWindow eps H,
          fBridgeG_h eps H h v p (residueProj eps H p ω) := rfl
  rw [hpt, integral_finsetSum Finset.univ (fun p _ => Integrable.of_finite)]
  exact Finset.sum_congr rfl (fun p _ => fBridgeG_h_mean eps H h p)

/-- **Concentration on the shifted decoupled diagonal** (the `h`-port of
`fBridge_concentration_decoupled`): for a `‖·‖ ≤ 1` window pattern, `F_h` deviates from the
shifted two-point correlation by `≥ δ` with probability
`≤ 2 exp(−δ² / (2(ε²H + 1)(2/ε² + 1)²))` — the `h = 1` exponent unchanged, since the variance
proxy never sees the offset.  Substitution of `fBridgeG_h_mean` into
`fBridge_h_concentration`. -/
theorem fBridge_h_concentration_decoupled (h : ℕ)
    {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (heps : 0 < eps)
    (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF_h eps H h v ω - ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
            ∑ j ∈ Finset.range H,
              (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ)|}
      ≤ 2 * Real.exp (-δ ^ 2 /
          (2 * (((eps : ℝ) ^ 2 * (H : ℝ) + 1) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2))) := by
  have hmean : (∑ p : primeWindow eps H,
        (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
          fBridgeG_h eps H h v p (residueProj eps H p ω)])
      = ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) :=
    Finset.sum_congr rfl (fun p _ => fBridgeG_h_mean eps H h p)
  have hq := fBridge_h_concentration eps H h hv heps hne hδ
  rw [hmean] at hq
  exact hq

end Salt.Entropy.Chowla
