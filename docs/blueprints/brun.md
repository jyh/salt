# Blueprint: Brun's theorem

**Target** (`Salt/Brun.lean`, `BrunStatement`):

```
Summable (Set.indicator {p : ℕ | p.Prime ∧ (p + 2).Prime} fun n => (1 : ℝ) / n)
```

The sum of reciprocals of twin primes converges — the counterpoint to mathlib's
`not_summable_one_div_on_primes`. **No completed formalization exists in any
major proof assistant** (survey 2026-07). First flag of the ladder.

## Route

Selberg Λ² sieve applied to the values `n(n+2)`, `n ≤ N`, sifting by primes
`< z`, yielding the sharp counting bound

```
twinPrimeCounting N = O(N / (log N)²)          (TwinCountingBigO, M5)
```

then Abel summation (`summable_mul_of_bigO_atTop`) to convergence (M6).

**Design decision — Mertens-free main term.** Mathlib has *no* Mertens
theorems (recon 2026-07: only qualitative divergence of Σ1/p and Chebyshev
Θ-bounds). The classical `S(z) ≫ (log z)²` main-term bound is therefore proved
via the divisor function: geometric expansion of `∏(1-ν(p))⁻¹` reduces `S(z)`
to `Σ_{m<z, odd} 2^Ω(m)/m ≥ Σ_{m<z, odd} τ(m)/m ≥ (Σ_{a<√z, odd} 1/a)² ≳ (log z)²`,
needing only harmonic-number bounds (`Mathlib/NumberTheory/Harmonic/`).
Everything stays inside present-day mathlib.

**Design decision — crude error term.** We need any power saving, not
sharpness: for squarefree `d`, `6^ω(d) ≤ d³`, so with level `y = N^{1/5}`,
`z = √y = N^{1/10}`, the error is `≤ Σ_{d<y} d³ ≤ y⁴ = N^{4/5}`. No divisor-sum
asymptotics (also absent from mathlib) required.

## What mathlib provides (exact names, pinned checkout v4.32.0-rc1)

- `Mathlib/NumberTheory/SelbergSieve.lean`: `BoundingSieve`, `SelbergSieve`
  (NB: `level` field currently **inert** — no theorem uses it),
  `siftedSum_le_mainSum_errSum_of_upperMoebius`, `lambdaSquared`,
  `upperMoebius_lambdaSquared`, `selbergTerms` (= g),
  `inv_selbergTerms_eq_sum_divisors_moebius_nu`,
  `nu_inv_eq_sum_divisors_inv_selbergTerms`,
  `sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv`,
  `mainSum_lambdaSquared_eq_sum_mul_sum_sq` (diagonalization; last decl in file).
  ⚠ Module docstring names are stale (`…of_UpperBoundSieve`,
  `upperMoebius_of_lambda_sq`, `lambdaSquared_mainSum_eq_diag_quad_form` do not
  exist) — cite the names above.
- Abel summation: `sum_mul_eq_sub_integral_mul₁`, `summable_mul_of_bigO_atTop`
  (`Mathlib/NumberTheory/AbelSummation.lean`); worked template:
  `Chebyshev.primeCounting_eq_theta_div_log_add_integral`.
- Asymptotics: `isLittleO_log_rpow_rpow_atTop`, `summable_of_isBigO_nat`,
  `summable_of_sum_range_le`, p-series `Real.summable_one_div_nat_rpow`.
- Counting: `Nat.count`, `Nat.primeCounting`, `Nat.primesBelow`;
  CRT: `ZMod.chineseRemainder`; squarefree API; `ArithmeticFunction` +
  `IsMultiplicative` + `arith_mult` tactic; `Nat.card_divisors`.

**Missing (we build):** everything below. Also note
[FLDutchmann/SelbergSieve](https://github.com/FLDutchmann/SelbergSieve)
(Mellendijk's pre-mathlib repo) proved a fundamental-theorem form
(`selberg_bound_simple`-style) — **check current state + license, attribute,
prefer porting over re-proving for M1**, and coordinate upstreaming.

## Lemma DAG

Classes per `docs/MODEL_POLICY.md`: A = Haiku/Sonnet, B = Sonnet/Opus,
C = Opus (+review), D = Fable+human. Node IDs are stable references.

### M0 — statements (done, this commit)
| id | statement | class |
|---|---|---|
| N0.1 | `twinPrimeCounting : ℕ → ℕ` via `Nat.count` | A |
| N0.2 | `TwinCountingBigO`, `BrunStatement` : Prop | A |

### M1 — Selberg endgame (the missing fundamental theorem)
Hardest cluster. Port/adapt from FLDutchmann if viable, else re-prove
(Heath-Brown notes; the required Möbius identities are already in mathlib).
| id | statement | deps | class |
|---|---|---|---|
| N1.1 | truncated optimal weights `w` supported on `{d ∣ P, d < √y}`, def + `w 1 = 1` | — | B |
| N1.2 | `∀ d, |w d| ≤ 1` | N1.1 | C |
| N1.3 | `mainSum (lambdaSquared w) = 1 / G(√y)` where `G(t) = Σ_{l ∣ P, l < t} selbergTerms l` (uses the three inversion identities + diagonalization) | N1.1 | C |
| N1.4 | **fundamental theorem**: `siftedSum ≤ totalMass / G(√y) + Σ_{d ∣ P, d < y} 3^ω(d) * |rem d|` | N1.2, N1.3, `siftedSum_le_mainSum_errSum_of_upperMoebius`, `upperMoebius_lambdaSquared` | C |

### M2 — twin-prime instantiation
| id | statement | deps | class |
|---|---|---|---|
| N2.1 | `rho d := #{n : ZMod d // n * (n + 2) = 0}` (def, `d ≥ 1`) | — | A |
| N2.2 | `rho` multiplicative on coprime moduli (via `ZMod.chineseRemainder`) | N2.1 | B |
| N2.3 | `rho 2 = 1`; `rho p = 2` for odd prime `p` (roots `0, p−2`) | N2.1 | B |
| N2.4 | progression count: `|#{n ∈ Icc 1 N : (d:ℕ) ∣ n*(n+2)} − N * rho d / d| ≤ rho d` | N2.1 | B |
| N2.5 | `n ↦ n*(n+2)` strictly mono on ℕ; `support := (Icc 1 N).image (· * (· + 2))` well-defined, card = N | — | A |
| N2.6 | `BoundingSieve` instance: `nu d = rho d / d` as `ArithmeticFunction ℝ`, `nu_mult` (from N2.2, `arith_mult`), `0 < ν(p) < 1` on `p ∣ P` (from N2.3), `totalMass = N` | N2.2–N2.5 | B |
| N2.7 | `|rem d| ≤ rho d ≤ 2^ω(d)` for squarefree `d` | N2.3, N2.4 | B |

### M3 — main term, Mertens-free: `G(z) ≥ c (log z)²`
| id | statement | deps | class |
|---|---|---|---|
| N3.1 | `selbergTerms p = ν(p)/(1−ν(p)) ≥ 2/p` for odd `p ∣ P`; `≥ 1` for `p = 2` | N2.6, `selbergTerms_apply` | A |
| N3.2 | expansion: `G(z) ≥ Σ_{m < z, m odd} ν*(m)` where `ν*(∏p^a) = ∏ν(p)^a` (group `m` by radical; `(1−ν)⁻¹ = Σ ν^j` finite truncation) | N3.1 | C |
| N3.3 | `τ(m) ≤ 2^Ω(m)`, hence `ν*(m) ≥ τ(m)/m` for odd `m` (`Nat.card_divisors`) | — | B |
| N3.4 | `Σ_{m<z, odd} τ(m)/m ≥ (Σ_{a<√z, odd} 1/a)²` (divisor pairing `ab = m`) | — | B |
| N3.5 | `Σ_{a≤t, odd} 1/a ≥ (log t)/2 − C` (harmonic bounds, `Mathlib/NumberTheory/Harmonic/` — verify exact names) | — | B |
| N3.6 | `∃ c₀ > 0, ∀ z ≥ z₀, G(z) ≥ c₀ * (log z)²` | N3.2–N3.5 | B |

### M4 — error term
| id | statement | deps | class |
|---|---|---|---|
| N4.1 | `6^ω(d) ≤ d³` for squarefree `d` (since `6 ≤ p³` for every prime) | — | A |
| N4.2 | `Σ_{d ∣ P, d < y} 3^ω(d) * |rem d| ≤ Σ_{d<y} 6^ω(d) ≤ y⁴` | N2.7, N4.1 | A |

### M5 — assembly: the counting bound
| id | statement | deps | class |
|---|---|---|---|
| N5.1 | twin `p` with `z < p ≤ N` ⇒ `p*(p+2)` coprime to `P(z)` ⇒ counted by `siftedSum` | N2.5 | B |
| N5.2 | `twinPrimeCounting N ≤ N / G(N^{1/10}) + N^{4/5} + N^{1/10} + O(1)` (apply N1.4 with `y = N^{1/5}`) | N1.4, N2.6, N3.6, N4.2, N5.1 | B |
| N5.3 | `TwinCountingBigO` (absorb lower-order terms; `isLittleO_log_rpow_rpow_atTop`, Chebyshev.lean idiom) | N5.2 | B |

### M6 — summability bridge
| id | statement | deps | class |
|---|---|---|---|
| N6.1 | `IntegrableAtFilter (fun t => 1/(t * (log t)²)) atTop` (antiderivative `−1/log t`) | — | B |
| N6.2 | **`BrunStatement`** via `summable_mul_of_bigO_atTop` with `c` = twin indicator, `f = 1/·` (template: `Chebyshev.primeCounting_eq_theta_div_log_add_integral`) | N5.3, N6.1 | B |
| N6.3 | (bonus) `brunConstant := ∑' …` def + positivity | N6.2 | A |

## Process

- Work happens on branch `brun`; `sorry` allowed there, never on `main`.
  Nodes merge to `main` only sorry-free and axiom-audited.
- Cascade per `docs/MODEL_POLICY.md`; every node result logs tokens.
  Estimated total inference: $50–150 (M1 dominates).
- M1/N3.2 are the review-gated nodes; if the FLDutchmann port is clean,
  M1 drops a class.
- Upstreaming: M1 (fundamental theorem) and M3 (Mertens-free G-bound) are
  mathlib-worthy independent of Brun; plan PRs once stable.
