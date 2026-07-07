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
n ≡ ν₀ (mod W), N ≤ n < 2N by w(n) = (Σ_{d : dᵢ ∣ n+hᵢ} λ_d)², λ built
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

### M2 — sieve design + k-dimensional machinery
| id | statement | deps | class |
|---|---|---|---|
| N2.0 | ★ **design freeze (Fable/human)**: fix f, T, A concretely; verify on paper that mains factor exactly, the overshoot Markov argument closes, and the ratio target M > 5 is reachable at k₀; amend M3–M6 statements accordingly | N3.1 probe | D (Fable) |
| N2.1 | index set `𝒟 R W` = {r : Fin k → ℕ | ∀i squarefree rᵢ, pairwise coprime, coprime to W, ∏rᵢ < R}; membership API, finiteness | — | B |
| N2.2 | `lam y : (Fin k → ℕ) → ℝ` from tensor y (Maynard (5.4)-style change of variables), support ⊆ 𝒟 | N2.1 | B |
| N2.3 | size bound: `max |lam y d| ≤ C_k · y_max · (1 + log R)^k` | N2.2 | C |
| N2.4 | ★ S₁ diagonalization: `Σ_{d,e} lam_d lam_e / ∏ᵢ [dᵢ,eᵢ] = Σ_r y_r² / ∏ᵢ φ(rᵢ)` (coordinatewise induction on the `SelbergPort` template) | N2.2 | C |
| N2.5 | S₂^{(m)} diagonalization: same with d_m = e_m = 1 and the transformed `y^{(m)}` (tensor ⇒ explicit 1-dim reweighting in coordinate m) | N2.4 | C |

### M3 — the 1-dimensional atoms
| id | statement | deps | class |
|---|---|---|---|
| N3.1 | ★ **probe**: `Σ_{r<x, squarefree, (r,B)=1} 1/φ(r) = (φ(B)/B)·log x + O_B(1)` — lower `≥ (φ(B)/B)(log x − C_B)` and upper `≤ (φ(B)/B) log x + C_B` (fallback: upper `≤ C_B(1+log x)` acceptable, report which); radical-decomposition route (`N = r·m, r = rad N` unique) per `M3Expansion` | — | C |
| N3.2 | Mertens-upper: `Σ_{p ≤ x} 1/p ≤ log log x + C` (Chebyshev θ-bound + Abel summation) | — | B |
| N3.3 | the truncated weighted atoms for the frozen f (log-power / g-sampled weights; exact statements from N2.0) | N2.0, N3.1 | C |
| N3.4 | `Σ_{q<Q} μ²(q) L^{ω(q)} / φ(q) ≤ (C log Q)^L` for fixed L (3 and 9 needed) | N3.2 | B |

### M4 — S₁
| id | statement | deps | class |
|---|---|---|---|
| N4.1 | per-(d,e) congruence count: `#{n ∈ [N,2N) : n ≡ ν₀ (W), [dᵢ,eᵢ] ∣ n+hᵢ ∀i} = N/(W ∏[dᵢ,eᵢ]) + O(1)` (CRT + `congCount_bound`) | N1.4, N2.1 | B |
| N4.2 | S₁ error: `Σ_{d,e} |lam lam| · O(1) ≤ C_k y_max² (log R)^{2k} R² = o(N)` for R = N^{1/5} | N2.3 | B |
| N4.3 | ★ S₁ main: exact tensor factorization into products of N3.3 atoms + Markov overshoot bound | N2.4, N3.3, N4.1 | C |

### M5 — S₂ and the hypothesis
| id | statement | deps | class |
|---|---|---|---|
| N5.1 | S₂^{(m)} decomposition: prime counts `primesCount` in progressions mod `W ∏[dᵢ,eᵢ]` (d_m = e_m = 1), main + per-modulus error | N2.5, N4.1 | C |
| N5.2 | ★ **EH consumption**: `Σ_{q < R²W} μ²(q) 3^{ω(q)} max_a |π-error(q,a)| ≤ N/(log N)^A` via Cauchy–Schwarz between N3.4 and `EH (1/2)`, with N0.2 as the trivial factor | N0.2, N0.3, N3.4 | C |
| N5.3 | S₂ main: tensor factorization + overshoot (the m-coordinate contributes the `(Σ f/φ)²`-shaped factor) | N2.5, N3.3, N5.1, N5.2 | C |

### M6 — the ratio: 1-dimensional calculus
| id | statement | deps | class |
|---|---|---|---|
| N6.1 | closed forms/bounds for the g(t) = 1/(1+At) integrals-and-sums the frozen f needs (`∫g²`, `∫g`, log-weighted variants) | N2.0 | B |
| N6.2 | ratio bound: `M(f, k, R) > 5` at the concrete k₀ (Prop-4.3-style: the log k − 2 log log k − 2 mechanism, all 1-dim) | N6.1 | C |
| N6.3 | concrete k₀ arithmetic (`log k₀` bounds via `norm_num`-friendly log estimates) | N6.2 | B |

### M7 — assembly
| id | statement | deps | class |
|---|---|---|---|
| N7.1 | `S₂ − S₁ > 0` for all large N, given `EH (1/2)`, at k₀ (chain M4 + M5 + M6 mains/errors) | N4.3, N5.3, N6.2, N6.3 | C |
| N7.2 | pigeonhole: `S₂ > S₁ ⇒ ∃ n ∈ [N,2N), ≥ 2 of n+hᵢ prime`; infinitude over all windows | N7.1 | B |
| N7.3 | **target `BoundedGapsFromEH`**: `EH (1/2) → ∃ C, …` with C = diam k₀ | N7.2 | B |
| N7.4 | (bonus) liminf form: `EH (1/2) → liminf (p_{n+1} − p_n) ≤ diam k₀` via `Nat.nth` | N7.3 | B |

## Process

- Track branch `maynard`; `sorry` allowed there, never on `main`. Nodes
  land sorry-free + axiom-audited, docs updated in the same commit
  (CLAUDE.md workflow step 5; guide file `maynard-guide.md` to be created
  when M1 opens, mirroring `brun-guide.md`'s card contract).
- **Order**: N3.1 (probe) runs FIRST — it is dispatchable immediately and
  its outcome gates N2.0, the Fable design freeze that fixes every M3–M6
  statement. M0/M1 are probe-independent and can proceed in parallel.
- Statement changes: N2.0 is the *designated* amendment point (Fable);
  after the freeze, iron rule 1 applies to M3–M6 statements like any
  others.
- Cascade per `docs/MODEL_POLICY.md`. Class profile: 2×A, 15×B, 12×C,
  1×D(design) — roughly 3× Brun's C-mass. Estimated inference $150–500;
  3–7 Brun-scale working days. Keystones: N2.4 (diagonalization), N4.3
  (exact-mains discipline), N5.2 (EH consumption), N2.0 (design).
- Upstreaming candidates independent of the target: N3.1 (the μ²/φ atom),
  N3.2 (Mertens upper bound), N3.4, and the k-dim Möbius toolkit.
