# Rung 5 opener — the large sieve → BDH → Vaughan (`largesieve`)

*Fable, 2026-07-11. Scoped per `next-rung-scoping.md` Rung 5 and ratified by
the user: done = character-form large sieve + Barban–Davenport–Halberstam +
Vaughan's identity (the identity + Type I/II reduction; the BV assembly and
Siegel–Walfisz input are the NEXT rung). Track branch `largesieve`. First
node: the W1 de-risking probe.*

## Doctrine

1. **Constant-factor everywhere.** No sharp `N + δ⁻¹` (needs Beurling–Selberg,
   absent from mathlib, and nothing downstream wants it). Loose explicit
   numerals (`7N` for `2πN`, etc.) are ENCOURAGED where they simplify
   `norm_num` work. Every constant explicit from day one — the Maynard track's
   ∃-opacity lesson is standing policy.
2. **Route: Gallagher, not duality/Selberg.** The Selberg/Boas–Bellman route
   costs a `log R` in the spacing sum that only smoothing removes; the CRUDE
   (coefficient-2) Gallagher lemma gives `Δ = δ⁻¹ + 4πN` with nothing but FTC,
   Cauchy–Schwarz, and finite Parseval — all mathlib-elementary. Frozen as
   `δ⁻¹ + 13N` (`13 ≥ 4π`). (Adversarial pass 2026-07-11: the sharp `2πN`
   needs the coefficient-1 triangular-weight lemma AND frequency re-centering
   — neither is in the DAG; the original frozen `7N` was UNPROVABLE via the
   chain. Nobody downstream cares about the factor.)
3. Iron rules as in `CLAUDE.md` (classify-then-prove; ≤3 attempts then flag;
   no sorry on the track's landed nodes; axiom budget
   `[propext, Classical.choice, Quot.sound]`; blueprint statements frozen —
   changes are Fable-tier).
4. Namespace `Salt.LS`, files `Salt/LS/*.lean`, aggregated by `Salt/LS/All.lean`
   and wired into `Salt.lean` at rung close (bare `lake build` must cover the
   track from the first commit — wire `All.lean` in immediately, extend as
   files land).

## Carrier choices (Fable-frozen; executor latitude only where marked)

- `e : ℝ → ℂ := fun x => Complex.exp (2 * Real.pi * Complex.I * x)`.
- Trig polynomial: `expSum (N : ℕ) (a : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * e (n * α)`. The `Ico M (M+N)` offset version is
  a corollary (`a ↦ a ∘ (· + M)` twist), NOT a separate development.
- Circle distance: `dist₁ (x y : ℝ) : ℝ` = distance from `x − y` to the
  nearest integer. Executor latitude: implement via `|x − y − round (x−y)|`
  or mathlib's `AddCircle` norm — whichever makes N4's disjointness cleanest —
  but the SPEC is: `dist₁ x y ≤ 1/2`, symmetric, invariant under integer
  shifts of either argument, and `dist₁ (a/q) (a'/q') ≥ 1/(q*q')` provable.
- δ-spaced system: `Spaced (δ : ℝ) (α : Fin R → ℝ) : Prop :=
  ∀ r s, r ≠ s → δ ≤ dist₁ (α r) (α s)`.
- Reduced residues: reuse `Nat.Coprime` filters consistent with
  `Salt/Maynard`'s `maxDiscrepancy` conventions where they touch.

## The node DAG

```mermaid
graph TD
  L0[L0.1-3 defs: e, expSum, dist₁/Spaced] --> L1
  L0 --> L2
  L1[L1.1 orthogonality ∫e=δ₀ / L1.2 Parseval] --> L3
  L2[L2.1 deriv expSum / L2.2 Parseval for S'] --> L3
  L0 --> L4[L4.1 Sobolev-Gallagher pointwise lemma]
  L4 --> L3
  L5[L5.1 spacing ⇒ disjoint δ-intervals mod 1<br/>L5.2 periodic unfolding Σ∫ ≤ ∫₀¹] --> L3
  L3[L3.1 ANALYTIC LS: Δ = δ⁻¹ + 13N] --> L6
  F[L6.1 Farey spacing 1/Q²] --> L6
  L6[L6.2 ARITHMETIC LS] --> L7
  G[L7.1 τ(χ) inversion for primitive χ<br/>L7.2 |τ|²=q] --> L7
  L7[L7.3 CHARACTER LS, primitive, q/φ(q)-weighted] --> L8
  L8[L8.1 conductor descent<br/>L8.2 ΣΛ² ≤ Cx log x<br/>L8.3 char orthogonality → residue variance<br/>L8.4 BDH] --> DONE1[BDH]
  V[L9.1 Vaughan identity<br/>L9.2 Type I shape<br/>L9.3 Type II bilinear shape<br/>L9.4 AP-discrepancy reduction] --> DONE2[Vaughan]
```

## Node catalog

Legend: class A/B/C per `CLAUDE.md`; ✅ proved / 🔄 in flight / ⬜ open / ⛔ flagged.

### W0 — statements (this document + `Salt/LS/Defs.lean`)
| id | statement | class | status |
|---|---|---|---|
| L0.1 | `e`, `expSum` defs + trivia (`‖e x‖ = 1`, `e (x+1) = e x`, `e`-additivity) — `Salt/LS/Defs.lean`, `@[fun_prop]` continuity | A | ✅ |
| L0.2 | `dist₁` def + spec lemmas (symm, ≤ 1/2, int-shift invariance, triangle-ish `dist₁ x z ≤ dist₁ x y + dist₁ y z`) — `Salt/LS/Dist.lean`, round-based carrier, 9 lemmas | B | ✅ |
| L0.3 | `Spaced` def + `Spaced δ α → R ≤ 1/δ + 1`-style counting sanity (optional, drop if unused) | B | ⬜ |

### W1 — the de-risking probe (Opus, FIRST COMMITTED NODE)
| id | statement | class | status |
|---|---|---|---|
| L1.1 | `∫ α in (0:ℝ)..1, e ((n − m : ℤ) * α) = if n = m then 1 else 0` (orthogonality; ℤ-cast exponent) — `integral_e_int` + `integral_e_mul_conj` | B | ✅ |
| L1.2 | **Parseval**: `∫ α in (0:ℝ)..1, ‖expSum N a α‖^2 = ∑ n ∈ range N, ‖a n‖^2` — `parseval`, landed at B (expand-and-integrate; prove in ℂ, cast once) | B/C | ✅ |
| L4.1 | **Gallagher pointwise**: `f : ℝ → ℂ` differentiable on `[t₀ − δ/2, t₀ + δ/2]`, continuous deriv (executor latitude: `ContDiff ℝ 1` or explicit `HasDerivAt` hypotheses): `‖f t₀‖^2 ≤ δ⁻¹ * ∫ t in I, ‖f t‖^2 + 2 * ∫ t in I, ‖f t‖ * ‖deriv f t‖` (the constant 2 is fine — doctrine) — `gallagher_pointwise`, `ContDiff ℝ 1` form; the set↔interval integral conversions were the C-content (`norm_integral_le_integral_norm_uIoc` chain) | C | ✅ |

Side conditions: `expSum` is a finite sum of smooth terms — integrability via
`Continuous.intervalIntegrable`, no measurability nodes needed (state this in
the file docstring, don't let side goals balloon). De-risked by the
adversarial pass: L1.1 compiles against the pin via
`integral_exp_mul_complex` + `Complex.exp_int_mul_two_pi_mul_I` (verified).

**Probe verdict (2026-07-11): GO.** L1.2 landed at B, L4.1 at C as
classified; no node needed a second attempt; API pins held. Keystone risk
RETIRED — the Gallagher route is ratified and the duality fallback is closed.

### W2 — analytic large sieve
| id | statement | class | status |
|---|---|---|---|
| L2.1 | `deriv (expSum N a) = expSum N (fun n => 2πi·n·a n)` (finite sum of smooth terms) | B | ⬜ |
| L2.2 | Parseval for the derivative + `n ≤ N` crude bound: `∫₀¹ ‖deriv (expSum N a)‖^2 ≤ (2π N)^2 · Σ ‖a n‖^2` | B | ⬜ |
| L5.1 | `Spaced δ α` (with `δ ≤ 1/2`, points taken mod 1) ⇒ the open intervals `(α r − δ/2, α r + δ/2)` are pairwise disjoint mod 1 | C (bookkeeping) | ⬜ |
| L5.2 | periodic unfolding: `g` 1-periodic, `0 ≤ g`, intervals disjoint mod 1 ⇒ `∑ r, ∫_{I r} g ≤ ∫ t in x₀..x₀+1, g` | C (bookkeeping) | ⬜ |
| L3.1 | **ANALYTIC LS** (frozen): `Spaced δ α → 0 < δ → δ ≤ 1/2 → ∑ r, ‖expSum N a (α r)‖^2 ≤ (δ⁻¹ + 13 * N) * ∑ n ∈ range N, ‖a n‖^2` | C | ⬜ |

### W3 — arithmetic large sieve
| id | statement | class | status |
|---|---|---|---|
| L6.1 | **Farey spacing**: `a/q ≠ a'/q'` reduced, `q, q' ≤ Q` ⇒ `dist₁ (a/q) (a'/q') ≥ 1/Q^2` (mod-1 wraparound case: `qq' − |aq'−a'q|` is a nonzero integer — write the argument out) — `farey_spacing_core`/`farey_spacing`, `Salt/LS/Farey.lean`, coprimality-free | B | ✅ |
| L6.1b | Farey system assembly: enumerate `{(q,a) : q ∈ Icc 1 Q, a reduced}` as `Fin R → ℝ`, derive `Spaced (1/Q²)` from pairwise L6.1, reindex `∑_q∑_a ↔ ∑_r` (bookkeeping; adversarial pass: this is C, not part of a B node) | C | ⬜ |
| L6.2 | **ARITHMETIC LS** (frozen): for `2 ≤ Q`: `∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (Nat.Coprime q), ‖expSum N c (a/q)‖^2 ≤ (Q^2 + 13*N) * ∑ n ∈ range N, ‖c n‖^2` — the `Q = 1` case is a separate one-line Cauchy–Schwarz corollary (`δ = 1/Q² = 1` violates L3.1's `δ ≤ 1/2` gate; adversarial pass) | B | ⬜ |

### W4 — character form
| id | statement | class | status |
|---|---|---|---|
| L7.1 | primitive `χ` mod q: `χ n * gaussSum χ⁻¹-bar = ∑ a, χ-bar a * e (n*a/q)`-shape (align with mathlib's `gaussSum` API — executor reads `Mathlib/NumberTheory/GaussSum.lean` first; the ℝ/ℂ-additive-character bridge `e (a/q) ↔ ZMod.toCircle`/`stdAddChar` is THE risk here) | C | ⬜ |
| L7.2 | `‖gaussSum χ ψ‖^2 = q` for primitive χ mod q, **ALL q (composite included)**. ⚠️ Adversarial pass: mathlib's `gaussSum_mul_gaussSum_eq_card` is `[Field R]`-only (prime q) — USELESS here. Route via the general-modulus API that IS in the pin: `gaussSum_mulShift_of_isPrimitive` + `star_gaussSum_eq` + Parseval over residues (`Analysis/Fourier/ZMod.lean` bridge `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`). Real work. | C | ⬜ |
| L7.3 | **CHARACTER LS** (frozen shape): `∑ q ∈ Icc 1 Q, (q / φ q : ℝ) * ∑ χ primitive mod q, ‖∑ n ∈ range N, c n * χ n‖^2 ≤ (Q^2 + 13*N) * ∑ ‖c n‖^2` (for `2 ≤ Q`) | C | ⬜ |

### W5 — BDH
| id | statement | class | status |
|---|---|---|---|
| L8.1 | conductor descent: sums over all χ mod q ↦ primitive χ mod conductor, with the `q/φ(q)` bookkeeping (mathlib conductor/`isPrimitive` API) | C | ⬜ |
| L8.2 | `∑_{n ≤ x} Λ(n)^2 ≤ C·x·log x` (Chebyshev, reuse `Salt/Maynard` supply + mathlib `Chebyshev.lean`) | B | ⬜ |
| L8.3 | character orthogonality → residue-class variance identity: `∑_{a reduced} ‖ψ(x;q,a) − ψ(x)/φ(q)‖^2 = (1/φ q) ∑_{χ ≠ χ₀} ‖ψ(x,χ)‖^2` | B | ⬜ |
| L8.4 | **BDH** (frozen SHAPE; exact log powers executor-latitude, constants explicit): `∃ C, ∀ x Q, Real.sqrt x ≤ Q → Q ≤ x → ∑ q ∈ Icc 1 Q, ∑_{a reduced} ‖ψ(x;q,a) − ψ(x)/φ(q)‖^2 ≤ C * Q * x * (log x)^3`. ψ-form primary (Λ-weighted); a θ-form corollary tying to `Salt/Maynard`'s π-based `maxDiscrepancy` is a stretch node L8.5, non-blocking. | C | ⬜ |

### W6 — Vaughan
| id | statement | class | status |
|---|---|---|---|
| L9.1 | **Vaughan's identity** (frozen as an exact `ArithmeticFunction`/finite-sum identity): for `U, V ≥ 1`, `n > V`: `Λ n = (∑_{d ∣ n, d ≤ U} μ d * Real.log (n/d)) − (∑_{dc ∣ n, d ≤ U, c ≤ V} μ d * Λ c) + (∑_{dc ∣ n, d > U, c > V} μ d * Λ c)` — exact bracket placement per Vaughan; executor derives from `μ * log = Λ * 1`-side identities in mathlib's `ArithmeticFunction` | C | ⬜ |
| L9.2 | Type I shape: `∑_{n ≤ x} a₁(n) f(n)` rearranged to `∑_{d ≤ UV} (coef d) ∑_{m ≤ x/d} f(dm)` with `|coef d| ≤ log x` | B | ⬜ |
| L9.3 | Type II bilinear shape: the `d > U, c > V` piece as `∑_m ∑_k b_m c_k f(mk)` with dyadic ranges and `‖b‖₂, ‖c‖₂` controlled | C | ⬜ |
| L9.4 | AP-discrepancy reduction (frozen SHAPE): the character sum `∑_{n≤x} Λ(n) χ(n)` bounded by Type I + Type II pieces — the statement BV's dispersion step consumes. PB-floor: L9.1 alone closes the wave with L9.2–4 flagged. | C | ⬜ |

### W7 — close-out
Reconciliation sweep, axiom audit of the four headline theorems, `Salt.lean`
wiring check, guide/status updates, rung-close flags entry, merge decision
(user).

## PB-floors (per wave)
- W1: both probe nodes or STOP (see verdict rule).
- W2–W3: L3.1 + L6.2 are MUST; L0.3 droppable.
- W4: L7.3 MUST; if the additive-character bridge (L7.1) fights mathlib's API,
  the floor is L7.3 stated over `ZMod q → ℂ` characters with our own
  `e(a/q)`-bridge as an explicit hypothesis + flag (Fable revisits).
- W5: L8.4 MUST in ψ-form; L8.5 (θ/π tie) stretch.
- W6: L9.1 MUST; L9.2–4 floor to flags if the bilinear bookkeeping balloons.

## Statement-design decisions reserved to Fable
Δ-constant changes; `dist₁` carrier swap after W1 evidence; the L8.4 log
power once L8.1–8.3 land; any GEH/BV-facing interface shaping.
