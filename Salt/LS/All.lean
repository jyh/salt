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
import Salt.LS.GaussSum
import Salt.LS.PsiDefs
import Salt.LS.ArithmeticLS
import Salt.LS.CharLS
import Salt.LS.Vaughan
import Salt.LS.Conductor
import Salt.LS.BDHPrep

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
killed by the convolution `μ * (Λ_{≤V} * ζ) = Λ_{≤V}`); `GaussSum`
(L7.1/L7.2 — the Gauss-sum machinery: **`gaussSum_normSq`**
`‖gaussSum χ ψ‖² = q` for primitive `χ`, **all** `q` (composite included) via
Parseval-over-residues + `AddChar.sum_mulShift` orthogonality — dodging the
`[Field R]`-only `gaussSum_mul_gaussSum_eq_card`; the τ-inversion
`dirichlet_inversion`/`dirichlet_inversion'` from
`gaussSum_mulShift_of_isPrimitive` at `χ⁻¹`; and `stdAddChar_eq_e`, the
`ψ a = e (a.val / q)` bridge to the track carrier `e`). `CharLS` (L7.3 —
**`char_LS`**, the character-form large sieve `∑_q (q/φ q)·∑_{χ prim} ‖∑ c χ‖²
≤ (Q²+13N)·∑‖cₙ‖²` (`2 ≤ Q`): per modulus `char_LS_perQ` combines Gauss-sum
inversion `T χ = (∑ c χ)·τ(χ⁻¹)` with `‖τ‖²=q` and Plancherel over *all* `χ` via
second orthogonality `DirichletCharacter.sum_characters_eq`, restricts to
primitive `χ`, then bridges `S a = expSum N c (a.val/q)` and reindexes the
unit-`a` sum to the Farey filter to invoke `arithmetic_LS`). `Conductor` (L8.1 —
the BDH conductor-descent toolkit: `primitiveCharacter_apply_of_isUnit`
(χ agrees with its primitive character on the coprime part), the ψ-difference
crude bound **`norm_psiChi_sub_primitiveCharacter_le`** `‖ψ(x,χ)−ψ(x,χ⋆)‖ ≤
ω(q)·log x` via a prime-power fiber count + `DirichletCharacter.norm_le_one`,
with `primeFactors_card_le_logb` (`ω(q) ≤ logb 2 q`), and the φ double-counting
reduction `sum_inv_totient_dvd_le` from totient super-multiplicativity — the
standalone `∑ 1/φ ≤ C(1+log Q)` factor threaded as a hypothesis, see flags).
`BDHPrep` (L8.2/L8.3 — the crude second moment **`sum_vonMangoldt_sq_le`**
`ΣΛ² ≤ (log 4 + 4)·x·log x` via `Λ n ≤ log n ≤ log x` and mathlib's
`Chebyshev.psi_le_const_mul_self`, plus the residue-variance identity
**`variance_eq`** `Σ‖ψ(x;q,a)−ψ(x,χ₀)/φ(q)‖² = (1/φ(q))·Σ_{χ≠χ₀}‖ψ(x,χ)‖²`
via full character orthogonality `DirichletCharacter.sum_characters_eq`
(over *all* `χ`, not just primitive — `psiChi_eq_sum_psiAP` fibers `Icc 1 x`
by residue, `sum_normSq_psiChi_eq` is the Parseval assembly)).
-/
