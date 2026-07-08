# Blueprint: bounded gaps between primes, conditional on level of distribution

**Target** (`Salt/Maynard.lean`, to be created in M0):

```
BoundedGapsFromEH : EH (1/2) → ∃ C, ∀ N, ∃ p q, N < p ∧ N < q ∧ p ≠ q ∧
                      p.Prime ∧ q.Prime ∧ (q : ℤ) - p ∈ Set.Icc (-(C:ℤ)) C
```

where `EH θ` states the primes have level of distribution θ (a
Bombieri–Vinogradov-shaped hypothesis; BV itself, unformalized anywhere,
would instantiate θ = 1/2). Maynard's theorem (arXiv 1311.4600), in
load-bearing conditional form. **No load-bearing formalization exists in
any assistant** (recon 2026-07: the one sorry-free scaffold runs against a
mock hypothesis interface with no real π(x;q,a) content). Second rung of
the ladder; the machinery (multidimensional Selberg sieve) is shared by
every later rung toward TPC.

## Route

Fix an admissible k-tuple H = {h₁ < … < h_k}. Weight each
n ≡ ν₀ (mod W), N ≤ n < K₀N (K₀ = 64 per the freeze) by w(n) = (Σ_{d : dᵢ ∣ n+hᵢ} λ_d)², λ built
from free parameters y by the Maynard change of variables. Compare
S₂ = Σ_n (#{i : n+hᵢ prime})·w(n) against S₁ = Σ_n w(n): if S₂ > S₁ for
all large N, some n in every window has ≥ 2 primes among n+hᵢ, so gaps
≤ h_k − h₁ occur infinitely often. S₁ needs only counting; S₂'s error
consumes `EH`. The main-term ratio is governed by a 1-dimensional
variational quantity that grows like log k — so a large concrete k buys
unlimited slack in every constant.

**Design decision — everything constant is loose, k is huge.** We fix
θ = 1/2, R = N^{1/5} (needs only M-ratio > 5 rather than the sharp 4),
and a concrete k₀ ≈ 10⁶ with ~30% slack. Nobody needs gap 600, let alone
246; the deliverable is `∃ C` with C extractable and comically large.

**Design decision — the tuple is a theorem, not a computation.**
H = the first k primes greater than k. Admissibility: for p ≤ k no
element is ≡ 0 (all are primes > k ≥ p); for p > k there are more
residues than elements. No `decide`-certificates, no Engelsma tables.

**Design decision — fixed W.** Since k is fixed, take D₀ = max(k, h_k)
*constant* and W = primorial D₀ (reuse `primorial_squarefree`). The
classical D₀ = log log log N dance exists only to make constants clean;
ours don't need to be. ν₀ exists by admissibility + CRT.

**Design decision — tensor weights: exact mains, lossy errors.** The
recon flagged the keystone risk: per-variable losses in k-fold sums
compound as C^k against a prize of log k, so Brun-style loosening cannot
touch the main terms. Resolution: take y_r = ∏ᵢ f(rᵢ) (tensor product,
f a fixed explicit 1-dim weight sampled from Maynard's g(t) = 1/(1+At)
on a support of length T/k, T ≍ log k). Then every k-fold main term
factors **exactly** into products of 1-dimensional sums — no per-variable
approximation exists to compound. The support-overshoot (∏rᵢ ≥ R, the
part outside Maynard's simplex) and all arithmetic irregularities are
one-sided *error* terms, bounded by a Markov/second-moment argument where
looseness is harmless. The S₂/S₁ ratio is then a ratio of polynomials in
the *same* 1-dim atomic sums, so leading constants largely cancel — the
freeze of exactly which atomic estimates are needed, and with what error
quality, is the design node N2.0 (Fable-owned), gated on the N3.1 probe.

## What mathlib provides (pinned checkout v4.32.0-rc1, recon 2026-07)

- `Nat.primeCounting`, `Chebyshev.psi/theta` + both-direction bounds,
  Bertrand; **no PNT, no Mertens, no Siegel–Walfisz, no Vaughan** — none
  needed: everything analytic is either elementary or inside `EH`.
- `ArithmeticFunction` + `IsMultiplicative` + Möbius inversion
  (1-dim only; k-fold versions we build), `Nat.ArithmeticFunction.totient`
  API, squarefree/primorial API.
- `AbelSummation.lean` (whole toolkit, battle-tested in Brun M6/N6).
- `Finset` k-fold plumbing: `Fintype.piFinset`, `Finset.prod_sum`,
  `lmarginal`/Pi integrals if ever needed (design avoids measure theory).
- 1-dim calculus for N6: `intervalIntegral.integral_pow`, `∫ 1/x`,
  by-parts; `norm_num` factorial extension; concrete log bounds
  (`Real.log_two_gt_d9` etc.) for the k₀ arithmetic.
- **From our own repo** (`Salt/Brun/`): `SelbergPort.lean` (the 1-dim
  diagonalization template: `selbergWeights_diagonalisation`,
  `moebius_inv_dvd_lower_bound`, `sum_mul_subst`),
  `CongruenceCounting.lean` (`congCount_bound` — the per-progression
  counting interface for both S₁ and the trivial π(x;q,a) bound),
  `M5Assembly.primorial_squarefree`, the M3 radical-decomposition
  technique (`M3Expansion.lean`) for the N3.1 atom, and the M5BigO/N6
  Abel-summation idioms.

## Lemma DAG

Classes per `docs/MODEL_POLICY.md`. ★ = keystone. Statements here are
semi-formal; N2.0 freezes the M3–M6 statements after the probe and may
amend them (Fable-tier, logged).

### M0 — statements & the hypothesis
| id | statement | deps | class |
|---|---|---|---|
| N0.1 | `primesCount x q a` (= π(x;q,a)) def via `Nat.count`; monotonicity, `primesCount x 1 0 = π x` | — | A |
| N0.2 | trivial bound `primesCount x q a ≤ x/q + 1` (block counting; `congCount_bound`) | N0.1 | B |
| N0.3 | `EH θ : Prop` (∀ A > 0, `Σ_{q ≤ x^θ} max_{a ∈ (ZMod q)ˣ} |π(x;q,a) − π(x)/φ(q)|` is `O(x/(log x)^A)`); `EH` antitone in θ; targets `DHL k`, `BoundedGapsFromEH` | N0.1 | B |

### M1 — the tuple
| id | statement | deps | class |
|---|---|---|---|
| N1.1 | `Admissible (H : Finset ℕ)` def: ∀ p prime, ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a; shift/subset API | — | A |
| N1.2 | `H k` := the first k primes > k (via `Nat.nth Nat.Prime`); card = k, sorted, diameter `diam k` finite | — | B |
| N1.3 | `Admissible (H k)` (p ≤ k: residue 0 is omitted since all elements are primes > p; p > k: `card (ZMod p) > k`) | N1.1, N1.2 | B |
| N1.4 | W-trick: `W k := primorial (max k (diam k))`; ∃ ν₀, ∀ h ∈ H k, `Nat.Coprime (ν₀ + h) (W k)` (CRT across p ∣ W via N1.3) | N1.3, `primorial_squarefree` | B |

### N2.0 — the design freeze (DONE 2026-07-07, Fable; adversarially reviewed)

Frozen after the N3.1 probe and a three-reviewer adversarial panel
(flags.md 2026-07-07 N2.0 for the full record — the panel caught one
outright error in the draft freeze and eight repairs, all incorporated
below). **Parameters:** window n ∈ [N, K₀N) with K₀ := 64; R := N^{1/5};
g(u) := 1/(1+Au) on [0,T] with A := log k, T := k^{1/8}/log k;
f(r) := g(k·log r/log R) on [1, R^{T/k}]; y_r := (∏ᵢ f(rᵢ))·1_𝒟;
D₀ := max(k³, max(H k)) (Lean amended to match — the k³ floor is what
makes every poly(k)/D₀ correction O(1/k)); all N-thresholds absorbed
into N ≥ N₀(k). The target is pure-existence, so N₀(k) and k₀ may be
astronomical (the honest chain forces log k₀ in the thousands; M6 works
with abstract inequalities like k₀ := 2^{6000}, never numeric
evaluation).

**Decisions.**
- **D1 (probe suffices).** The exact-constant μ²/φ upper bound (the
  `(1*h)` convolution node in PhiAtom.lean's PORT-BLOCKER) is **not
  built**. Full consumption audit: B₁-lower-exact consumed once
  (squared) in the S₂ numerator; A₁-upper-4× exactly once in the final
  ratio slot; A₁⁽¹⁾/A₁⁽²⁾-upper-4× only in overshoot moments;
  A₁-lower at (1−o(1)) quality (free — decreasing-weight partial
  summation preserves the atom's exact lower constant); B₁-upper only
  at crude/fallback quality (λ_max, trivial errors). Nothing needs a
  rung the probe didn't land.
- **D2 (symbolic cancellation, mandated route).** S₁-upper and S₂-lower
  are stated against the same abstract A₁ sum, so exactly one lossy 4
  enters the ratio. Any route bounding mains per-coordinate (relative
  C^k or (log k)^k) is **forbidden at statement level** — in particular
  Maynard's general-y additive-y_max contraction (his Lemma 5.3 as
  stated) costs ((log k)/8)^{k−1}/k² relative with our fixed D₀ and is
  fatal; the tensor-specific multiplicative contraction (available
  since f is decreasing) is mandated.
- **D3 (empirical centering).** The overshoot second moment centers at
  c := A₁⁽¹⁾/A₁ (kills the mean-squared cross term identically; any
  fixed numeric center leaves Θ(1) from the factor-16 lossy-mean
  interval, unprovable from the frozen rungs). Threshold-gap constant
  3/4, not 1/2 (the 1/2 version has only O(1/log k) margin and fails
  outright for k ≲ 200). Resulting rate 64T/(Ak) → 0; the k−T variant
  (inner-sum truncation) works identically, gap ≥ 0.49k.
- **D4 (three correction families, all r-averaged).** (i) pairwise
  coprimality within one index: one-sided, ≤ (2k²/D₀)·main via the
  Σ_{p>D₀} p⁻² tail; (ii) inner-sum coprimality in y^{(m)}: pointwise
  bounds are FALSE (grow with N); use (B₁−L(r))² ≥ B₁² − 2B₁L(r) then
  r-average, ≤ (ck/(D₀log D₀))·main; (iii) cross-collision pairs
  (dᵢ,eⱼ) > 1 for i ≠ j (count is exactly 0, but the algebraic identity
  sums over them): bounded via the y-side representation at
  poly(k)/D₀ relative — never via |λ|-absolute sums (C^k, fatal).
- **D5 (window/endpoints).** Window length (K₀−1)N = 63N appears in
  S₁-main; S₂'s prime counts run at shifted endpoints x = N+h_m−1,
  K₀N+h_m−1, with an O_k(1) slop lemma |Δπ_m − Δπ| ≤ 2·max(H k). The
  binding EH-modulus constraint is at the smaller endpoint:
  W·N^{2/5} ≤ ⌊(N+h_m−1)^{1/2}⌋ for N ≥ (2W)^{10}. (True room is
  R = N^{1/4−δ}, not N^{1/4}.)

### M2 — k-dimensional machinery (general-y algebra)
| id | statement | deps | class |
|---|---|---|---|
| N2.1 | index set `𝒟 R W` = {r : Fin k → ℕ | ∀i squarefree rᵢ, pairwise coprime, coprime to W, ∏rᵢ < R}; membership API, finiteness | — | B |
| N2.2 | `lam y : (Fin k → ℕ) → ℝ` from y (Maynard (5.4) change of variables), support ⊆ 𝒟 | N2.1 | B |
| N2.3 | size bound: `max |lam y d| ≤ C_k · y_max · (1 + log R)^k` (the 4^k inside C_k is error-side only — harmless by design, do not "fix") | N2.2 | C |
| N2.4 | ★ S₁ diagonalization: `Σ_{d,e} lam_d lam_e / ∏ᵢ [dᵢ,eᵢ] = Σ_r y_r² / ∏ᵢ φ(rᵢ)` — exact algebra (`Σ_{u∣n} φ(u) = n`), coordinatewise on the `SelbergPort` template | N2.2 | C |
| N2.5 | ★ S₂^{(m)} diagonalization: `Σ_{d,e : d_m=e_m=1} lam lam / ∏ φ([dᵢ,eᵢ]) = Σ_{r, r_m=1} (y^{(m)}_r)² / ∏ᵢ g(rᵢ)` with **g(p) = p−2** totally multiplicative (forced: φ = 1 ∗ g by Möbius inversion; φ-denominators are UNPROVABLE as algebra — panel finding) and `y^{(m)}` the φ-weighted m-contraction per Maynard (5.8) | N2.4 | C |
| N2.6 | comparison lemmas: `g(r) ≤ φ(r)` and `φ(r)³ ≤ g(r)·r²` for squarefree r, least prime factor ≥ 3 (per-prime: `(p−2)p² ≥ (p−1)³ ⇔ p² ≥ 3p−1`) — restores literal-A₁ domination in S₂'s non-m coordinates, preserving D2's symbolic cancellation | — | A |
| N2.7 | congruence compatibility: (d,e) with some (dᵢ,eⱼ) > 1, i ≠ j has NO solution (p > D₀ ≥ diam H cannot divide hᵢ−hⱼ ≠ 0), count = 0; otherwise CRT-solvable with a reduced residue mod W∏[dᵢ,eᵢ] | N1.4 | B |

### M3 — the 1-dimensional atoms
| id | statement | deps | class |
|---|---|---|---|
| N3.1 | ★ **probe — DONE** (Salt/Maynard/PhiAtom.lean): `phiAtom_lower` (exact constant), `phiAtom_upper_lossy` (4×), `phiAtom_upper_fallback`. The exact-upper PORT-BLOCKER stays unbuilt per D1 | — | C ✅ |
| N3.2 | Mertens-upper: `Σ_{p ≤ x} 1/p ≤ log log x + C` (Chebyshev θ-bound + Abel summation) | — | B |
| N3.3 | weighted transfers, frozen: A₁ & B₁ lower at exact constant; A₁, A₁⁽¹⁾ (weight u·g²), A₁⁽²⁾ (u²·g²) upper at 4×; B₁ upper at fallback quality; explicit additive +C_W constants (never bare (1+o)); the unimodal weight u·g² splits at u = 1/A, the increasing weight u²g² uses boundary+integral partial summation (lands at exactly 4× under the T/A² yardstick) | N3.1 | C |
| N3.4 | `Σ_{q<Q} μ²(q) L^{ω(q)} / φ(q) ≤ (C log Q)^L` for fixed L — **consumed at L = 3k and L = 9k²** (the k-dim pair-multiplicity is (3k)^{ω}, not 3^ω) | N3.2 | B |
| N3.5 | Chebyshev interval: `π(64N) − π(N) ≥ c·N/log N` (from mathlib `theta_ge` + `theta_le_log4_mul_x` + `theta_eq_sum_primesLE`; margin 62·log 2, conspiracy is exactly at K₀ = 2) | — | B |

### M4 — S₁
| id | statement | deps | class |
|---|---|---|---|
| N4.1 | per-(d,e) congruence count on [N, K₀N): under N2.7's compatibility, `= (K₀−1)N/(W ∏[dᵢ,eᵢ]) + O(1)`; for collision pairs, `= 0` (CRT + `congCount_bound`) | N1.4, N2.1, N2.7 | B |
| N4.2 | S₁ trivial error: `Σ_{d,e} |lam lam| · O(1) ≤ C_k (log R)^{2k} R² = o(N/(log N)^anything)` — N^{3/5} headroom crushes all log powers | N2.3 | B |
| N4.3 | ★ S₁-main UPPER: `≤ ((K₀−1)N/W)·A₁^k + cross-collision + trivial error`, by two one-sided relaxations (drop 𝒟-truncation, drop pairwise coprimality — both only add nonneg terms) with A₁ symbolic | N2.4, N3.3, N4.1, N4.4 | C |
| N4.4 | cross-collision bound: the (dᵢ,eⱼ)>1 correction to S₁-main, via the y-side representation, `≤ (ck²/D₀)·A₁^k` relative (forced prime p > D₀ at the colliding coordinate pair) | N2.4, N2.7 | C |

### M5 — S₂ and the hypothesis
| id | statement | deps | class |
|---|---|---|---|
| N5.1 | S₂^{(m)} decomposition at shifted endpoints (x = N+h_m−1, K₀N+h_m−1): prime counts `primesCount` in progressions mod W∏[dᵢ,eᵢ] (d_m = e_m = 1 vanishing is EXACT — a divisor 1 < d < p of a prime is impossible since ∏dᵢ < R < N ≤ n+h_m), main + per-modulus error; slop lemma `|Δπ_m − Δπ| ≤ 2·max(H k)` | N2.5, N2.7, N4.1 | C |
| N5.2 | ★ **EH consumption**: `Σ_{q < R²W} μ²(q) (3k)^{ω(q)} maxDiscrepancy ≤ N/(log N)^A'` via Cauchy–Schwarz between N3.4 (L = 9k²) and `EH (1/2)` applied at both shifted endpoints with exponent A ≥ 9k² + O(k); N0.2 + π(x) ≤ x as the trivial factor | N0.2, N0.3, N3.4 | C |
| N5.3 | ★ y^{(m)} contraction, tensor-specific multiplicative route (D2): `y^{(m)}_r = β(r)·(∏_{i≠m} f(rᵢ))·B-inner(r)·(1 + O(k·ε₂))` with β(r) = ∏_{p ∣ ∏rᵢ}(1−(p−1)⁻²) ∈ [1−2k/D₀, 1] via the DISTINCT-primes Euler tail (per-factor bounds are useless — ω grows with N), ε₂ ≤ c/(D₀ log D₀); inner-coprimality loss r-AVERAGED via (B₁−L)² ≥ B₁²−2B₁L (D4.ii) | N2.5, N3.3 | C |
| N5.4 | overshoot/truncation: empirical-ratio-centered second moment (D3) — `Σ over {Σuᵢ ≥ k} ≤ (A₁⁽²⁾/A₁)·(4/k)·A₁^k/(1−c)²`-shape, c = A₁⁽¹⁾/A₁ ≤ 3/4, rate 64T/(Ak); k−T variant for the inner truncation (bulk tuples make it vacuous — u(a) < T always) | N3.3 | C |
| N5.5 | ★ S₂-main LOWER: `≥ (Δπ_min/φ(W))·B₁²·A₁^{k−1}·(explicit constant)·(1 − D4 corrections)` with literal A₁ via N2.6's pointwise domination; Δπ_min from N3.5 with the D5 slop lemma | N2.6, N3.5, N5.1, N5.2, N5.3, N5.4 | C |

### M6 — the ratio: 1-dimensional calculus
| id | statement | deps | class |
|---|---|---|---|
| N6.1 | closed forms: `I_g = log(1+AT)/A`, `J_g = T/(1+AT)`, `∫ug² = [log(1+X)−X/(1+X)]/A²`, `∫u²g² ≤ T/A²` unconditionally (via `log(1+X) ≥ X/(1+X)`); the two DISTINCT limits μ_u → 1/8 and I_g → 1/8 kept separate (they differ ~50% at k ~ 10⁵) | — | B |
| N6.2 | ratio bound: `Σ_m S₂^{(m)}/S₁ ≥ k·[c_cheb/((K₀−1)·64·4)]·(1/5)·A·I_g² ·(1 − constants) > 1` for k ≥ k₀, all constants explicit, A₁ symbolic throughout, k₀ ABSTRACT (2^{6000}-style; never numeric evaluation) | N6.1 | C |
| N6.3 | concrete k₀: the closed-form chain of N6.2 verified at the chosen k₀ via abstract log-inequalities | N6.2 | B |

### M7 — assembly
| id | statement | deps | class |
|---|---|---|---|
| N7.1 | `S₂ − S₁ > 0` for all large N, given `EH (1/2)`, at k₀ (chain M4 + M5 + M6 mains/errors) | N4.3, N5.3, N6.2, N6.3 | C |
| N7.2 | pigeonhole: `S₂ > S₁ ⇒ ∃ n ∈ [N,K₀N), ≥ 2 of n+hᵢ prime`; infinitude over all windows | N7.1 | B |
| N7.3 | **target `BoundedGapsFromEH`**: `EH (1/2) → ∃ C, …` with C = diam k₀ | N7.2 | B |
| N7.4 | (bonus) liminf form: `EH (1/2) → liminf (p_{n+1} − p_n) ≤ diam k₀` via `Nat.nth` | N7.3 | B |

## Process

- Track branch `maynard`; `sorry` allowed there, never on `main`. Nodes
  land sorry-free + axiom-audited, docs updated in the same commit
  (CLAUDE.md workflow step 5; guide file `maynard-guide.md` to be created
  when M1 opens, mirroring `brun-guide.md`'s card contract).
- **Order** (updated post-freeze, 2026-07-07): M0, M1, N3.1, N2.0 are
  DONE. Everything in M2–M3 (N2.1–N2.7, N3.2–N3.5) plus N6.1 is now
  unblocked and parallelizable; M4/M5/M6 chain behind them per the deps
  columns.
- Statement changes: N2.0 is the *designated* amendment point (Fable);
  after the freeze, iron rule 1 applies to M3–M6 statements like any
  others.
- Cascade per `docs/MODEL_POLICY.md`. Class profile: 2×A, 15×B, 12×C,
  1×D(design) — roughly 3× Brun's C-mass. Estimated inference $150–500;
  3–7 Brun-scale working days. Keystones: N2.4 (diagonalization), N4.3
  (exact-mains discipline), N5.2 (EH consumption), N2.0 (design).
- Upstreaming candidates independent of the target: N3.1 (the μ²/φ atom),
  N3.2 (Mertens upper bound), N3.4, and the k-dim Möbius toolkit.
