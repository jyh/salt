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

---

# Scoping the next rung (post-Maynard)

*Fable, 2026-07-09. Written the day `bounded_gaps_from_eh_complete :
BoundedGapsFromEH` merged to `main` (48eb541): Rung 3 above is DONE —
Maynard's theorem, machine-checked, conditional on EH(1/2), axiom-clean
`[propext, Classical.choice, Quot.sound]`. This section records what the
build taught us and ranks the rungs from here toward twin primes.*

## 1. What the Maynard build established (assets)

**Mathematical assets on `main`.** The full multidimensional Selberg
engine: k-dim weights + diagonalization (S2DiagLam/S2DiagRestricted),
Lemma 5.3 contraction with O(k) constants (Lemma53 + Lemma53Tight), the
collision/erasure machinery (CollisionQuant, S2Collision, VAbs,
EulerTailL), the (3k)^ω pair fiber count (S2FiberCount), EH consumption
(EHConsume, S2CompatEHFinal), sharp one-variable transfers
(Transfer/TransferSharp/RatioCore), Chebyshev-interval prime supply,
CRT/congruence counting, explicit Mertens/Rankin, and the pigeonhole
endgame (Endgame, Final, Complete). Roughly: everything a future
sieve-theoretic rung needs short of new analytic inputs.

**Methodological assets (the transferable ones).** Six fragilities were
caught across the track — per-u coprimality (false atom), budget split,
hA11 ≤ 1/4 (unprovable atom), colliding-pairs RHS (wrong by B₁²),
absolute-vs-relative Lemma-5.3 error (B-type vs A-type), and the 2^k
error constant (formalization looseness fatal only at the last atom).
Every one lived in the *assembly* of estimates, not in any single lemma.
The disciplines that caught them: (i) check satisfiability of every
atom/hypothesis before building on it; (ii) the B-vs-A dimensional check
(every error term carries the f₀-tensor weight); (iii) adversarial
verification of every landed node; (iv) EXPLICIT constants — ∃-bound
constants went opaque twice (R-uniformity, rankinC/mertensC) and had to
be re-derived; new analytic work should expose constants from day one.
Ops lesson: background Agents complete where parallel workflows stall on
long builds; module-scoped `lake build` only.

## 2. The hard ceiling of this method (why twins need new mathematics)

Two structural facts, both now visible *inside* our own formalization:

**M_k asymptotics.** The pigeonhole needs the sieve ratio (our
`ratio_core_lower`, informally Maynard's M_k ~ log k) to exceed 2m/θ for
m+1 primes at distribution level θ. Computed values: M₂ ≈ 1.38,
M₃ ≈ 1.65, M₄ ≈ 1.84, M₅ > 2. Twin primes is the k = 2 tuple {0,2};
even at the impossible-to-exceed θ = 1 it needs M₂ > 2. Not a loose
constant — a theorem-shaped wall. First reachable: k = 5 under EH(1/2)
⟹ gaps ≤ 12 (tuple {0,4,6,10,12}).

**The parity barrier (Selberg).** Divisor-sum-driven sieves cannot
distinguish even from odd numbers of prime factors. Polymath 8b: under
*generalized* EH the ε-enlarged sieve reaches gaps ≤ 6 ({0,2,6}) and
parity provably stops it there. The wall between 6 and 2 is not
engineering. Chen's theorem (p, p+2 = P₂) is the sieve pushed exactly to
this wall. **No refinement of what we built reaches twin primes.**

## 3. The rungs, ranked

### Rung 4a — Explicit gap: EH(1/2) → gaps ≤ 12 (recommended headline)
Replace the crude logarithmic weights `fWt` (which forced
k₀ ~ exp(7·10⁶/c)) with Maynard's genuine variational weights; formalize
M₅ > 2 as a finite-dimensional optimization — rational I_k/J_k closed
forms (Dirichlet integral: ∫∏tᵢ^{aᵢ} = ∏aᵢ!/(k+Σaᵢ)!) + a concrete
polynomial F + `norm_num`-grade certification. Replaces `ratio_prize`'s
asymptotic with an exact computation; turns "some C" into C = 12.
Est. Brun-scale. Class profile: B with one C-cluster (re-threading the
S₂ lower bound through polynomial weights).

### Rung 4b — Level-of-distribution interface refactor (shovel-ready, ~1 session)
Factor `EH`/`eh_error_pow` into a general "primes have level θ with a
(log x)^B haircut" interface consumed by the sieve. Our moduli sit at
W·N^{2/5} ≪ √N/(log N)^B, so the sieve side is unchanged. This makes the
theorem *BV-consumable*: the day BV lands (Rung 5), unconditionality is
an instantiation. Do this before or alongside 4a.

### Rung 5 — The large sieve → Bombieri–Vinogradov (unconditional gaps)
The pincer identified post-Brun, still correct: large sieve by duality +
Bessel (constant-factor version suffices), Farey spacing, character form
via |τ(χ)| = √q; then Vaughan's identity (unformalized anywhere) and the
Siegel–Walfisz-grade input (the deep end — watch PrimeNumberTheoremAnd's
progress on zero-free regions; Isabelle/AFP has the template). Payoff:
**unconditional bounded gaps** — the strongest headline available to
formalization today. Multi-quarter; the large-sieve module alone is
first-in-any-assistant and self-contained.

### Rung 6 — GEH → 6, plus the parity wall itself
State generalized EH (level of distribution for Dirichlet convolutions),
formalize the Polymath 8b ε-trick with k = 3 {0,2,6}. The deeper prize:
a *formal statement of the method's limit* — machine-checked "no sieve
of this class goes below 6." Novel meta-mathematics; needs careful
Fable-tier statement design to be honest and non-vacuous.

### Rung 7 — Chen's theorem (p, p+2 with p+2 = P₂)
The closest true theorem to twin primes. Linear sieve with bilinear
error terms + the switching principle. Monumental (multiple
Maynard-scale tracks); parity-consistent, so no wall in the way. The
natural flagship after BV exists.

### Rung 8 — Parity-breaking beachheads (the only road that could lead to 2)
Matomäki–Radziwiłł (multiplicative functions in short intervals) and
Tao's two-point logarithmic Chowla (λ(n)λ(n+1) → 0 on log-average, via
entropy decrement) are the only *proven* parity-breaking machinery.
Neither gives twins — the Liouville→von-Mangoldt chasm is open — but a
library holding our sieve stack + BV + MR + log-Chowla is the best
possible position for whenever the mathematical breakthrough arrives.
Nothing here is formalized anywhere. Moonshot-scale; scope only after
Rung 5.

**Twin primes itself: there is no proof to formalize.** Honest bottom
line. What formalization contributes now: (a) the verified library along
the known frontier; (b) the assembly discipline — a future proof will be
a cascade of hundreds of coupled estimates, exactly the failure mode our
pipeline catches.

## 4. Recommendation

**Rung 4b immediately** (one session, makes the artifact BV-ready), then
**Rung 4a as the next track branch** (`explicit12`): EH → 12 explicit is
the highest insight-per-node target and exercises the variational
machinery every later rung shares. Interleave **Rung 5's large-sieve
module** as the long-pole starter during 4a stalls (same pincer logic as
post-Brun). Rungs 6–8 are scoped, not scheduled.

Also queued (hygiene, Fable-tier, ~1 session): a consolidation sweep of
the endgame scaffolds — `Complete.lean` is the load-bearing capstone;
`Final.lean`'s conditional `bounded_gaps_from_eh`/`AnalyticFrontier` and
the superseded ∃-constant lemmas (`s2main_lower` original,
`S2InnerBoundQ`/`Qdiag_gv` section, `htail_bound` 2^k version, the
non-uniform `S1_upper_A1`/`S2m_ge_compatMain_eh`) should be marked
`deprecated`-by-docstring or pruned, and the maynard-guide.md status
cards reconciled to COMPLETE.
