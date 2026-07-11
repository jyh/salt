/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.Dist
import Salt.LS.Defs
import Salt.LS.Parseval
import Salt.LS.Gallagher
import Salt.LS.Farey
import Salt.LS.Deriv
import Salt.LS.Spacing
import Salt.LS.AnalyticLS
import Salt.LS.ArithmeticLS
import Salt.LS.Vaughan

/-!
# Rung 5 opener (`largesieve`) — aggregate import

The large sieve → BDH → Vaughan track. Design:
`docs/blueprints/largesieve.md`. Extended as modules land; wired into
`Salt.lean` from the first commit so the bare `lake build` covers the track.

Landed: `Dist` (L0.2 — the mod-1 circle distance `dist₁`, round-based,
full spec incl. triangle inequality and the integer-difference
characterization); `Defs` (L0.1 — the frozen carriers `e`/`expSum` +
trivia, `@[fun_prop]`-tagged continuity); `Parseval` (L1.1 orthogonality +
L1.2 **Parseval** `∫₀¹‖expSum‖² = Σ‖aₙ‖²`); `Gallagher` (L4.1 — the
Sobolev/Gallagher pointwise lemma, `ContDiff ℝ 1` form, frozen constant 2).
W1 probe verdict: GO — keystone risk retired, Gallagher route ratified.
`Farey` (L6.1 — `farey_spacing_core` at `1/(q·q')` + `farey_spacing` at
`1/Q²`, coprimality-free); `Deriv` (L2.1/L2.2 — `hasDerivAt_expSum`/
`deriv_expSum`/`contDiff_expSum` + the derivative Parseval bound
`(2πN)²`); `Spacing` (L5.1/L5.2 fused — `Spaced` + the periodic
disjoint-union bound `sum_integral_le_period`, sort-free min-window
route); `AnalyticLS` (L3.1 — **`analytic_LS`**, the analytic large sieve
`Δ = δ⁻¹ + 13N`, Young-inequality cross term, `π² ≤ 10` slack);
`ArithmeticLS` (L6.1b/L6.2 — the reduced Farey system `fareyPairs`/`fareyFrac`,
the reindexing engine `sum_expSum_sq_le_of_spaced`, and the arithmetic large
sieve **`arithmetic_LS`** `Q² + 13N` (`2 ≤ Q`) plus the `Q = 1`
Cauchy–Schwarz corollary `arithmetic_LS_one`); `Vaughan` (L9.1 —
**`vaughan`**, Vaughan's identity as an exact `ArithmeticFunction`/finite-sum
decomposition of `Λ n` for `n > V`, plus the `f : ℕ → ℂ`-weighted summed form
`vaughan_sum`; direct divisor double-counting with the `n > V` guard term
killed by the convolution `μ * (Λ_{≤V} * ζ) = Λ_{≤V}`).
-/
