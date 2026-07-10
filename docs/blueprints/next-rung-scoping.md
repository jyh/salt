# Scoping the next rung (post-Brun)

*Fable, 2026-07-07. Recon: four-agent sweep over the local mathlib pin
(360da6fa, 2026-06-18), external Lean/Isabelle artifacts, and a full
ingredient inventory for the Maynard-conditional candidate. Raw findings:
session scratchpad `rung-recon/*.json`; the load-bearing facts are
reproduced here.*

## 1. The facts that constrain the choice

**What mathlib has (relevant strengths).** A mature Dirichlet-character
layer (conductor/primitivity, full orthogonality, Gauss sums, functional
equation, L(χ,s) ≠ 0 on re s ≥ 1); the new `Chebyshev.lean` (2025) with
ψ/θ/π bounds of the right order in both directions; the complete
Abel-summation toolkit we used in M6; Fourier on ℝ with Plancherel and
Poisson; Bessel + adjoint/C*-identity duality; Fubini/`lmarginal`/Pi
integration over `[0,1]^k`; `norm_num` factorial automation; Euler
products; the harmonic/Euler–Mascheroni corner.

**What mathlib lacks (all confirmed absent).** PNT in any form. Mertens
I/II/III. Vaughan's identity. Siegel–Walfisz or *any* uniformity in the
modulus. Zero-free regions. The large sieve. Farey/well-spaced machinery.
Exponential-sum estimates. Multiplicative mean-value theorems
(Wirsing/Shiu). Admissible tuples. Anything multidimensional in sieve
theory (`SelbergSieve.lean` still stops before the fundamental theorem —
our `SelbergPort.lean` remains ahead of mathlib).

**External state.**
- **PrimeNumberTheoremAnd** (Apache-2.0, active daily, tagged to mathlib
  v4.31.0): has ψ ~ x, ψ = x + O(x·exp(−c(log x)^{1/10})), PNT-in-AP for
  *fixed* modulus, and vendors the full Selberg sieve + interval
  Brun–Titchmarsh (q = 1) sorry-free. **Nothing Siegel–Walfisz-shaped
  anywhere in Lean.** StrongPNT (classical remainder) still has sorries —
  Isabelle/AFP got that layer first (Song–Yao 2025).
- **Nobody in any assistant** has: the large sieve, Bombieri–Vinogradov,
  Maynard–Tao in load-bearing form, or Chen. Even Vaughan's identity is
  unformalized. Two 0-star Lean scaffolds for bounded gaps exist; the
  more serious one (sorry-free Maynard combinatorics) runs against a
  *mock* BV interface — confirming both the demand and the gap.
- AFP has the analytic-layer templates (Dirichlet L, PNT+remainder,
  Pólya–Vinogradov) but **zero sieve theory**.

**Ingredient audit for Maynard-conditional** (bounded gaps assuming a
level-of-distribution hypothesis): hypothesis statement A; admissibility
A/B (decidable checks, greenfield but easy); pigeonhole endgame A/B;
finite optimization B *if* I_k/J_k are defined as rational closed forms
(Dirichlet's ∫∏t_i^{a_i} = ∏a_i!/(k+Σa_i)!, `norm_num` + factorial
extension finishes) — no interval arithmetic needed; the k-dimensional
Selberg machinery is a greenfield C-cluster with our `SelbergPort.lean`
as the direct 1-dim template; and the **keystone risk** is the main-term
evaluation: Brun-style constant-loosening does **not** transfer naively,
because per-variable losses in the k-fold sums compound as C^k against a
prize of only log k. Mitigation identified: Maynard's own structure keeps
main terms *exact* through the k-fold induction (products of exact
one-variable mean values) and is lossy only in error terms, and the
one-variable atom — Σ_{r<R, (r,W)=1} μ²(r)/φ(r) = (φ(W)/W)·log R + O_W(1)
— is Mertens-free elementary via the μ²/φ divisor decomposition plus
mathlib's harmonic bounds. That is *exactly* our M3 technique scaled up.
Roughly a third of the engine room (Möbius manipulation, congruence
counting, W-trick primorial API, harmonic bounds, Abel/BigO glue) is
already proved in this repo.

## 2. The options, ranked

### Option 1 — Maynard–Tao, conditional on level of distribution (recommended)

**Statement (target shape).** Define `EH θ` := the primes have level of
distribution θ (a Bombieri–Vinogradov-shaped Σ-max error bound, stated
with our own π(x;q,a)/θ(x;q,a) definitions — an A-node). Prove: for the
explicit admissible k₀-tuple H and explicit polynomial F,
`EH (1/2) → ∀ N, ∃ n > N, at least 2 of {n+h₁, …, n+h_{k₀}} are prime`,
hence `EH (1/2) → liminf (p_{n+1} − p_n) ≤ diam H`. Constants loose by
doctrine: k₀ is ours to choose (bigger k buys slack — the log k prize vs
any fixed evaluation loss), and the gap bound is whatever diameter falls
out; nobody needs 600, let alone 246.

**Benefits.** The headline artifact: *bounded gaps between primes,
machine-checked, modulo BV* — the moment anyone formalizes BV, ours
becomes unconditional by instantiation. It is the genuine next rung of
the TPC ladder (multidimensional sieve = the machinery all later rungs
share). First-in-the-world in load-bearing form. Maximal reuse of Brun
assets. Zero deep-analytic input — the entire proof is elementary given
the hypothesis, which is precisely what our cascade is good at.

**Downsides / risks.** Big: est. 60–90 nodes across ~9 milestones,
i.e. 5–10 Brun-scale days. Two genuine C-keystones: (i) the k-dim
diagonalization cluster, (ii) the mean-value cluster with the
"exact mains, lossy errors" discipline — a design bar Brun never faced.
One prior scaffold exists (mock-interface repo), so "first" needs the
qualifier "load-bearing" (their analytic core is a placeholder; ours
would be a real theorem about a real hypothesis).

**De-risking probe (do first, ~1 session):** prove the one-variable atom
Σ_{r<R,(r,W)=1} μ²(r)/φ(r) ≥ (φ(W)/W)·log R − C_W *and* the matching
upper bound with explicit error, in isolation. If that lands at
B/C-as-expected, the keystone risk is retired before the blueprint is
even ratified.

### Option 2 — The AP toolkit: Mertens I–III + arithmetic-progression Brun–Titchmarsh

Mertens' three theorems (from Chebyshev + Abel summation; III's e^{−γ}
via the existing Euler–Mascheroni/ZetaAsymp corner) plus
π(x;q,a) ≤ C·x/(φ(q)·log(x/q)) by re-instantiating our own Selberg
engine over a progression (the q = 1 interval case is a worked template
in PNT+/Mellendijk; the AP version exists nowhere).

**Benefits.** High-confidence, Brun-sized or smaller (~15–25 nodes,
mostly B). Fills confirmed mathlib holes; strong upstreaming package
together with M1. Exercises the exact primes-in-APs muscle later rungs
need. **Downsides.** Lateral: no new machinery toward Maynard (whose
core proof needs neither Mertens nor BT); delays the headline.

### Option 3 — The large sieve inequality (+ Barban–Davenport–Halberstam)

Analytic large sieve by duality + Bessel (constant-factor version —
mathlib's adjoint/C*-identity and Fourier tooling suffice; the sharp
N + δ⁻¹ needs absent Beurling–Selberg extremal functions, skip it),
Farey spacing (elementary, greenfield), the multiplicative-character
form via |τ(χ)| = √q (one step from mathlib's
`gaussSum_mul_gaussSum_eq_card`), and BDH variance as the payoff
corollary. ~20–30 nodes, one C-keystone.

**Benefits.** First-in-any-assistant, fully self-contained, and the
hard prerequisite of BV — the strategic complement to Option 1 (Option 1
consumes BV's *conclusion*; Option 3 starts building BV's *proof*).
**Downsides.** Delivers no theorem about primes by itself; BDH variance
is the consolation statement, not a headline.

### Option 4 — Bombieri–Vinogradov itself: ruled out for now

Needs large sieve (Option 3) + Vaughan's identity (absent, medium) +
Siegel–Walfisz-grade uniform input — which exists in **no** Lean
artifact and sits on zero-free-region theory that even PNT+ still has
sorried (Isabelle only got that layer in 2025). Multi-quarter scale.
Revisit after Options 1 and 3.

## 3. Recommendation

**Blueprint Option 1 (Maynard-conditional) as Rung 3 of the ladder**, on
a new track branch `maynard`, opening with the de-risking probe as its
first committed node. Slot Option 3 (large sieve) as Rung 4 — it can be
interleaved during Option-1 stalls, and together they form the pincer on
BV (Rung 5+): Option 1 makes BV's conclusion *consumable*, Option 3
starts making it *provable*. Option 2 stays on the shelf as a quick
upstreaming win whenever one is wanted; its pieces get built on demand
if any Maynard node turns out to want them.

Draft milestone skeleton for the Option-1 blueprint (to be formalized
into `maynard.md` node tables on ratification):

| Milestone | Content | Class profile |
|---|---|---|
| W0 | Statements: π/θ(x;q,a), `EH θ`, admissibility, targets | A/B |
| W1 | Admissible-tuple API + the concrete k₀-tuple (decidable checks) | A/B |
| W2 | **Probe**: the one-variable μ²/φ mean value with explicit error | B/C |
| W3 | k-dim Selberg weights: λ from y, diagonalization, size bounds | C cluster |
| W4 | k-fold mean-value induction ("exact mains, lossy errors") | C keystone |
| W5 | S₁ evaluation (main term + EH-controlled error) | C |
| W6 | S₂ evaluation (per-component prime sums) | C |
| W7 | Rational I_k/J_k, explicit F, `norm_num` M_k > 4 finish | B |
| W8 | Pigeonhole, liminf endgame, `EH → BoundedGaps` assembly | A/B |
| W9 | (stretch) Maynard Prop 4.3: M_k ≥ log k − 2 log log k, the ∀θ form | C |

Statement-design decisions reserved to Fable/human at blueprint time:
the exact `EH θ` formulation (ψ vs θ vs π; max over residues; Q-range),
fixed-(θ = 1/2, m = 2) vs the ∀θ form (W9), and the choice of k₀/F with
deliberate slack.
