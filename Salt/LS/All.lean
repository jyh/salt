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
import Salt.LS.DvdLS
import Salt.LS.Vaughan
import Salt.LS.Conductor
import Salt.LS.BDHPrep
import Salt.LS.PhiSum
import Salt.LS.TypeSums
import Salt.LS.BDH
import Salt.Tactic.AuditAxioms

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
`PhiSum` (L8.1b — the standalone φ-double-counting factor
**`sum_inv_totient_le`** `∑_{m ∈ Icc 1 Q} 1/φ(m) ≤ 4·(1 + log Q)`: the general-`m`
one-sided identity `1/φ(m) ≤ ∑_{d ∣ m} μ²(d)/(m·φ(d))` via the radical
`rad m` and `Salt.Maynard.sum_divisors_inv_totient_ge`, the `Finset.sum_comm`
divisor swap, and `harmonic_le_one_add_log` + reuse of
`Salt.Maynard.sum_inv_mul_totient_le` (`≤ 4`); plus the composed corollary
**`sum_inv_totient_dvd_le'`** that discharges the `hphi` hypothesis of
`Conductor.sum_inv_totient_dvd_le` — making the L8.1 bound unconditional for L8.4).
`TypeSums` (L9.2/L9.3/L9.4 — the Type I/II reduction of Vaughan's identity:
the reindex engine `reindex_core` (`sum_comm'` + per-`d` bijection `n ↔ d·m`,
freeing all `n.divisors`); **`typeI_one_eq`**/**`typeI_two_eq`** (Type I —
`Σ₁ = ∑_{d≤U} μ(d) ∑_m (log m) f(dm)` and the `t = d·c` collapse
`Σ₂ = ∑_t a(t) ∑_m f(tm)` via AF-associativity `sigma2_inner`, coefficient
`typeICoeff` with `abs_typeICoeff_le` `|a(t)| ≤ log t` and support
`typeICoeff_eq_zero`); **`typeII_eq`** (Type II bilinear —
`Σ₃ = ∑_{d>U} μ(d) ∑_m b(m) f(dm)`, `typeIIData` with
`typeIIData_nonneg`/`typeIIData_le_log`; the landed `vaughan`'s `Σ₃` is the
`d·c ∣ n` residual form, so the faithful bilinear packaging folds the `>V`
data into `b(m) = ∑_{c∣m,c>V}Λc` rather than the node prose's `Λ(c)`);
**`tail_decomp`** (general-`f`
`∑_{V<n≤x} Λ(n) f(n) = TypeI₁ − TypeI₂ + TypeII`) and the character reduction
**`psiChi_sub_head_eq`** with head bound `norm_head_le` (`‖head‖ ≤ V·log V`)
and multiplicativity `chi_cast_mul`).
`BDH` (L8.4 — **`bdh`**, Barban–Davenport–Halberstam in the pure large-sieve
Barban form: `∑_{q ≤ Q} ∑_{a reduced} ‖ψ(x;q,a) − ψ(x,χ₀)/φ(q)‖² ≤
6000·(Q·x + x²)·(log x)²` for `2 ≤ Q ≤ x`). Assembly: `variance_eq` per modulus →
conductor descent `‖ψ(x,χ)‖² ≤ 2‖ψ(x,χ⋆)‖² + 2‖ψ(x,χ)−ψ(x,χ⋆)‖²` → the error
piece (`Conductor` crude bound + character count `card_eq_totient`, closed by
`(log x)² ≤ 4x`) plus the main piece: the injective primitive-pair regrouping
`regroup` (`χ ↦ ⟨conductor χ, χ.primitiveCharacter⟩`, left inverse `changeLevel`),
the `(q,f)` swap (`Finset.sum_comm'` + `PhiSum.sum_inv_totient_dvd_le'`), and the
dyadic block bound `dyadic` (fibre by `Nat.log 2 (f-1)`, per block `CharLS.char_LS`
at level `2ʲ⁺¹` via the `psiChi ↔ range (x+1)` bridge `charLS_psi`). Verified
numeral `≈ 5792 ≤ 6000`.
-/

/-! ## ⭐ THE TRACK'S AXIOM GATE (added 2026-08-26, math)

⛔ **WHY THIS BLOCK EXISTS: UNTIL TODAY THIS AGGREGATE AUDITED NOTHING.**  A census run for the
helm's carried-debt order (`seat/briefs/2026-08-26-math-REPORT-uncovered-set.md`) found that
`Salt/LS/All.lean` and `Salt/Twelve/All.lean` were **the only two track aggregates in the repo with
no `#audit_axioms` block at all** — every other `*/All.lean` carries one.  The track built green and
**nothing checked its axioms**, which is the precise shape of *a dead branch reading as coverage*:
`lake build` going green says the track ELABORATES, never that it is axiom-clean.

⇒ 🔑 ***A GREEN BUILD IS NOT A GATE. THE GATE IS THE AUDIT, AND AN AGGREGATE WITHOUT ONE IS AN
UNGATED TRACK WEARING A GATE'S FILENAME.***

Listed below are the track's TERMINALS — the results other tracks would consume — not every
declaration.  That is a deliberate first cut, chosen so the block is honest about its own scope:
**this gate covers the named results, and the track's helper lemmas are covered only through
them.**  Widening it is cheap and welcome. -/
open Salt.Tactic in
#audit_axioms Salt.LS.parseval
  Salt.LS.gallagher_pointwise
  Salt.LS.farey_spacing_core
  Salt.LS.farey_spacing
  Salt.LS.analytic_LS
  Salt.LS.arithmetic_LS
  Salt.LS.arithmetic_LS_one
  Salt.LS.char_LS_perQ
  Salt.LS.char_LS
  Salt.LS.vaughan
  Salt.LS.vaughan_sum
  Salt.LS.bdh
