# Brun's theorem — reader's guide

<!--
MAINTENANCE RULES (contract; see CLAUDE.md workflow step 5 + iron rule 5)

Who may edit what:
  - All prose sections (§1-§5) and every card's **Statement.** / **Role.**
    field: Fable/human sessions ONLY. These are the immutable shadow of the
    blueprint statements (iron rule 1 applies to them).
  - Card volatile fields (**Proof idea. Lean. Status. Difficulty. Notes.**),
    Mermaid status classes/emoji, and the §0 frontier list: any tier, as
    part of landing or flagging a node (same commit as the proof — workflow
    step 5).
  - The §0 strategic line: Fable/human only.

Status tokens (used identically in cards, graphs, and the briefing):
  ✅ proved (sorry-free, axiom-audited)   🟡 partial (Status line says which part)
  🔴 open                                 ⛔ tier-blocked (attempted; see flags)
  🔬 research-keystone annotation (may combine with 🔴/⛔)

Card grammar (parsed by scripts/blueprint_lint.py — keep it exact):
  #### N<x>.<y> — <short name> <status token>
  **Statement.** <prose; immutable>
  **Role.** <prose; immutable>
  **Proof idea.** <actual if proved, "(expected)" if open>
  **Lean.** `fully.qualified.name` (file); ... | — not started
  **Status.** <token> <detail; date; tier, attempts>
  **Difficulty.** predicted <class>[, actual <assessment>]
  **Notes.** <optional>
  Open/blocked cards must cite NO backticked names in the Lean field.
  Lean-trench gotchas do NOT go in cards — they live in flags.md; link by date.

Green lint = "not mechanically stale", never "the prose is true".
Statement fidelity is guaranteed by the immutability rule above, not by tooling.
-->

## 0. Briefing

*Updated: 2026-07-07 (Fable).*

- **State**: 16 of 27 nodes proved (+1 partial). M0, M2, M4 complete;
  M3 lacks only N3.2→N3.6; M5/M6 have their sieve-facing halves done.
- **Frontier** (open, all deps met): **N1.1** (B) · **N3.2** (C).
- **Next step**: N1.1 — adapt `selbergWeights` from the Mellendijk repo
  (cached; see R1/A1), prove `w 1 = 1`.
- **Blockers**: everything else in M5/M6 waits on N1.4 (via the M1 port)
  and N3.6 (via N3.2).
- **Strategic line**: M1 was feared as open-ended research; the 2026-07-07
  recon reduced it to a C-class port of `amellendijk/selberg-sieve4` (see R1).
  Land N1.1 first to validate the port route end-to-end on the easiest piece.

## 1. Big picture

**The project (salt).** A machine-checked proof of the Twin Prime Conjecture
is the aspirational objective (`TwinPrimeConjecture`, Salt/Basic.lean). Nobody
knows how to prove TPC; the project's honest form is a ladder of frontier
formalizations — sieve theory first, then (if the ladder holds) toward
Bombieri–Vinogradov and Maynard–Tao. Each rung is a real, self-contained
mathematical artifact.

**This track (Brun).** The first rung: **Brun's theorem** — the sum of
reciprocals of twin primes converges (`BrunStatement`), in pointed contrast
to mathlib's divergence of Σ 1/p over all primes. Per the 2026-07 survey in
the blueprint, **no completed formalization exists in any major proof
assistant** — Mellendijk's Lean 4 sieve repo names it as its end-goal but its
twin-prime file is a stub. Completing it is an announceable first.

**What "done" means.** A `theorem` of type `BrunStatement` with no `sorry`,
kernel-checked, whose axioms are exactly mathlib's standard three
(`propext`, `Classical.choice`, `Quot.sound`). The kernel is the referee;
this guide is only the map.

**The payoff en route.** Three mathlib-worthy pieces independent of Brun
itself: the ported Selberg fundamental theorem (M1), the Mertens-free
main-term bound (M3), and the congruence-counting module. Plus a dataset:
every node records predicted vs. actual difficulty across the model-tier
cascade — raw material for an experience report on LLM-driven formalization.

## 2. The route, and why this route

**Sifting twins.** Fix `N` and a threshold `z`. For `n ∈ [1, N]` form the
products `n(n+2)`. If `n > z` is a twin-prime leader (both `n` and `n+2`
prime), then `n(n+2)` has **no** prime factor `≤ z`. So the number of twin
leaders in `(z, N]` is at most the number of `n ∈ [1, N]` whose `n(n+2)`
survives sifting by every prime `≤ z` — the *sifted count* — and the twins
below `z` cost only `+z` to add back. Everything reduces to an upper bound
on the sifted count.

**The Selberg Λ² upper bound.** For any real weights `λ` supported on
divisors of `P = ∏ p ≤ z` with `λ₁ = 1`, the square
`(Σ_{d ∣ gcd(m, P)} λ_d)²` is `≥ 1` when `m` is coprime to `P` and `≥ 0`
always — so its sum over the support dominates the sifted count. Expanding
the square gives `(main coefficient)·N + remainder`, where the main
coefficient is a quadratic form in `λ`. Selberg's move: the form
diagonalizes over indices `ℓ ∣ P` and can be minimized exactly subject to
`λ₁ = 1`; truncating the support to `d² ≤ y` keeps the remainder sum finite.
The minimum is `1/S` where `S = Σ_{ℓ ∣ P, ℓ² ≤ y} g(ℓ)` — classically
written `G(√y)` with `G(t) = Σ_{ℓ ∣ P, ℓ < t} g(ℓ)`, and `S ≥ G(√y)` since
`g > 0`, so lower bounds for `G` transfer — with
`g(ℓ) = ∏_{p ∣ ℓ} ν(p)/(1 − ν(p))`. For twins the local density is
`ν(d) = ρ(d)/d`, with `ρ(d)` the number of roots of `n(n+2) ≡ 0 mod d`:
`ρ(2) = 1`, `ρ(p) = 2` for odd `p`. Net:

> π₂(N) ≤ N / S + Σ_{d ∣ P, d ≤ y} 3^ω(d) |R_d| + z + O(1).

**Design decision 1 — Mertens-free main term.** The classical lower bound
`G(z) ≫ (log z)²` goes through Mertens' theorems, and mathlib has none of
them (recon 2026-07: only qualitative divergence of Σ 1/p). Instead we go
through the divisor function: expanding each `(1 − ν(p))⁻¹` as a finite
geometric series and grouping integers by radical converts `G(z)` into
`Σ_{m < z odd} ν*(m)` with `ν*(∏p^a) = ∏ν(p)^a`; for odd `m` this is
`2^Ω(m)/m ≥ τ(m)/m`; and a bare-hands divisor pairing plus mathlib's
harmonic-number bounds give `Σ_{m<z, odd} τ(m)/m ≥ (Σ_{a<√z, odd} 1/a)²
≳ (log z)²` with explicit constants. The only analytic input is
`Mathlib/NumberTheory/Harmonic/`.

**Design decision 2 — crude error term.** The sharp bound on
`Σ_{d<y} 3^ω(d)|R_d|` uses divisor-sum asymptotics — also absent from
mathlib. But we need *any* power saving, not sharpness:
`|R_d| ≤ ρ(d) ≤ 2^ω(d)`, so each term is `≤ 6^ω(d) ≤ d³` for squarefree
`d`, and the whole sum is `≤ y⁴`. With `y = N^{1/5}` that is `N^{4/5}` —
negligible against `N/(log N)²`, with exponent slack to spare (any
`y = N^θ`, `θ < 1/4`, works).

**Endgame.** Abel summation (`summable_mul_of_bigO_atTop`, template
`Chebyshev.primeCounting_eq_theta_div_log_add_integral`) converts
`π₂(N) = O(N/(log N)²)` into convergence of `Σ 1/p`.

**Rejected routes.** (i) Mertens-based main term — upstreaming Mertens first
is a bigger project than the workaround. (ii) Sharp error via divisor
asymptotics — same. (iii) Brun's original pure sieve — avoids the Λ²
optimization entirely, but its truncated inclusion–exclusion is messier and
has no mathlib scaffolding; retained as fallback A2, not the mainline.

## 3. Risk register

**R1 — the Selberg optimization (N1.2–N1.4).** *Severity: was critical, now
medium (recon 2026-07-07).* Mathlib's `SelbergSieve.lean` stops one step
short: Λ² bound, upper-Möbius property, and diagonalization are there; the
optimal-weight choice and the `mainSum = 1/G(√y)` identity are not. The
recon found the missing step fully worked out in `amellendijk/selberg-sieve4`
(Mellendijk; formerly `FLDutchmann/SelbergSieve`; Apache-2.0; dormant since
2024-05): `selbergWeights`, `selberg_bound_weights` (|w| ≤ 1),
`selberg_bound_simple` (the fundamental theorem, exactly our N1.4 shape).
Decisively: mathlib's file *is* that repo's `SieveLemmas.lean`, upstreamed —
the name mapping is known, so only `Selberg.lean` (~440 lines) needs porting
across ~2.5 years of mechanical API drift (repo pins Lean v4.7.0-rc2).
Residual risks: drift worse than it looks; mathlib's `level` field is inert
(no theorem uses it), so the truncation machinery comes wholly from the port.
Key files cached in the session scratchpad. *Current thinking: port (A1),
after checking for in-flight upstream PRs (A3).*

**R2 — the geometric expansion (N3.2).** *Severity: medium-high.* The
radical-grouping argument (`G(z) ≥ Σ ν*(m)`) is the one C-node with no
template anywhere: finite geometric expansion of `∏(1−ν(p))⁻¹`, reindexing
by radical, truncation bookkeeping. Multiplicative-function and
`Finsupp`-heavy. Fallback: A4.

**R3 — mathlib API friction.** *Severity: low, chronic.* Pinned at
v4.32.0-rc1. Already bitten once by stale docstrings naming nonexistent
declarations (blueprint warns). Renames (`Finset.card_insert_of_notMem`,
…) cost small constant time per node. The pin means upstream refactors of
`SelbergSieve.lean` don't hit us mid-track; the price is paid once at
toolchain bumps.

**R4 — assembly arithmetic (N5.2, N5.3).** *Severity: medium.* Every term
is proved but the gluing is `rpow`/`log` bookkeeping with the `⌊x⌋₊` Big-O
idiom — historically error-prone tactics work. Mitigations: exponent slack
(θ < 1/4), Chebyshev.lean as the worked template, and all inputs already
kernel-checked.

**R5 — the summability glue (N6.2).** *Severity: low-medium.* The bridge
from `twinPrimeCounting` (a `Nat.count`) to the `Set.indicator` sum in
`BrunStatement` is exactly the kind of off-by-one/coercion mismatch that
surfaces late. Same template as R4.

## 4. Alternatives, if the path fails

**A1 (primary, for R1): port `Selberg.lean`.** Apache-2.0 with attribution
(file headers + README credit to Mellendijk). ~440 lines against an
already-upstreamed foundation. The repo's `BrunTitchmarsh.lean` and
`PrimeCountingUpperBound.lean` are complete worked applications — the best
available templates for our M5 assembly too.

**A2 (fallback, for R1): Brun's pure sieve.** Truncated inclusion–exclusion;
no optimization step at all. Yields the weaker `π₂(N) ≪ N(log log N)²/(log N)²`,
which still suffices for M6 (the Abel integrand stays convergent). Cost:
fresh combinatorial estimates (binomial truncation bounds) with no mathlib
scaffolding; adopt only if the port dies.

**A3 (parallel, for R1): coordinate upstream.** The repo's trajectory
suggests `Selberg.lean` was headed for mathlib. Before porting, check for
in-flight PRs (search mathlib4 PRs for "Selberg"); if one exists, help land
it instead of duplicating.

**A4 (fallback, for R2): squarefree-part decomposition.** Instead of
grouping by radical, write each odd `m < z` uniquely as `m = ℓk²` with `ℓ`
squarefree; the `ν*`-sum transfers to squarefree support with a `Σ 1/k²`
loss factor. Sketch only — unverified; adopt only if radical grouping
stalls.

**A5 (if all sieve routes stall).** There is no A5 — the sieve *is* the
track. A total stall means re-planning at Fable/human level, and the honest
statement of that is more useful than a fake fallback.

## 5. Roadmap

| Milestone | One line | State |
|---|---|---|
| M0 | Formal targets: π₂, `TwinCountingBigO`, `BrunStatement` | 2/2 ✅ |
| M1 | Selberg fundamental theorem (the engine) | 0/4 🔴 → port route |
| M2 | Twin instantiation: ρ, its laws, the `BoundingSieve` | 7/7 ✅ |
| M3 | Main term, Mertens-free: `G(z) ≳ (log z)²` | 4/6 🟡 |
| M4 | Error term: crude `y⁴` power saving | 2/2 ✅ |
| M5 | Assembly: `π₂(N) = O(N/(log N)²)` | 1/3 🟡 |
| M6 | Abel summation → `BrunStatement` | 1/3 🟡 |

```mermaid
flowchart LR
  M0["M0 targets 2/2 ✅"]
  M1["M1 fundamental thm 0/4 🔴"]
  M2["M2 twin sieve 7/7 ✅"]
  M3["M3 main term 4/6 🟡"]
  M4["M4 error term 2/2 ✅"]
  M5["M5 counting bound 1/3 🟡"]
  M6["M6 summability 1/3 🟡"]
  M2 --> M3
  M2 --> M4
  M2 --> M5
  M1 --> M5
  M3 --> M5
  M4 --> M5
  M5 --> M6
```

Node-level DAG (edges = blueprint direct dependencies; legend:
green ✅ proved · yellow 🟡 partial · grey 🔴 open · red border 🔬 keystone):

```mermaid
flowchart TB
  classDef done fill:#c8e6c9,stroke:#2e7d32,color:#111
  classDef partial fill:#fff9c4,stroke:#f9a825,color:#111
  classDef open fill:#eeeeee,stroke:#9e9e9e,color:#111
  classDef keystone fill:#eeeeee,stroke:#c62828,stroke-width:3px,color:#111

  subgraph SM0["M0 — targets"]
    N0_1["N0.1 ✅ π₂ def (A)"]:::done
    N0_2["N0.2 ✅ targets (A)"]:::done
  end
  subgraph SM1["M1 — fundamental theorem"]
    N1_1["N1.1 🔴 weights (B)"]:::open
    N1_2["N1.2 🔴🔬 |w|≤1 (C)"]:::keystone
    N1_3["N1.3 🔴🔬 mainSum=1/G (C)"]:::keystone
    N1_4["N1.4 🔴🔬 fund. thm (C)"]:::keystone
  end
  subgraph SM2["M2 — twin sieve"]
    N2_1["N2.1 ✅ ρ def (A)"]:::done
    N2_2["N2.2 ✅ ρ mult (B)"]:::done
    N2_3["N2.3 ✅ ρ at primes (B)"]:::done
    N2_4["N2.4 ✅ progression count (B)"]:::done
    N2_5["N2.5 ✅ support (A)"]:::done
    N2_6["N2.6 ✅ BoundingSieve (B)"]:::done
    N2_7["N2.7 ✅ |R|,ρ bounds (B)"]:::done
  end
  subgraph SM3["M3 — main term"]
    N3_1["N3.1 ✅ g at primes (A)"]:::done
    N3_2["N3.2 🔴 ν* expansion (C)"]:::open
    N3_3["N3.3 🟡 τ≤2^Ω (B)"]:::partial
    N3_4["N3.4 ✅ divisor pairing (B)"]:::done
    N3_5["N3.5 ✅ odd harmonic (B)"]:::done
    N3_6["N3.6 🔴 G≥c·log² (B)"]:::open
  end
  subgraph SM4["M4 — error term"]
    N4_1["N4.1 ✅ 6^ω≤d³ (A)"]:::done
    N4_2["N4.2 ✅ error sum≤y⁴ (A)"]:::done
  end
  subgraph SM5["M5 — assembly"]
    N5_1["N5.1 ✅ twins sifted (B)"]:::done
    N5_2["N5.2 🔴 counting bound (B)"]:::open
    N5_3["N5.3 🔴 TwinCountingBigO (B)"]:::open
  end
  subgraph SM6["M6 — summability"]
    N6_1["N6.1 ✅ integrability (B)"]:::done
    N6_2["N6.2 🔴 BrunStatement (B)"]:::open
    N6_3["N6.3 🔴 Brun constant (A)"]:::open
  end

  N1_1 --> N1_2
  N1_1 --> N1_3
  N1_2 --> N1_4
  N1_3 --> N1_4
  N2_1 --> N2_2
  N2_1 --> N2_3
  N2_1 --> N2_4
  N2_2 --> N2_6
  N2_3 --> N2_6
  N2_4 --> N2_6
  N2_5 --> N2_6
  N2_3 --> N2_7
  N2_4 --> N2_7
  N2_6 --> N3_1
  N3_1 --> N3_2
  N3_2 --> N3_6
  N3_3 --> N3_6
  N3_4 --> N3_6
  N3_5 --> N3_6
  N2_7 --> N4_2
  N4_1 --> N4_2
  N2_5 --> N5_1
  N1_4 --> N5_2
  N2_6 --> N5_2
  N3_6 --> N5_2
  N4_2 --> N5_2
  N5_1 --> N5_2
  N5_2 --> N5_3
  N5_3 --> N6_2
  N6_1 --> N6_2
  N6_2 --> N6_3
```

## 6. Lemma catalog

### M0 — targets

#### N0.1 — twin-prime counting function ✅
**Statement.** π₂(n) is the number of primes p ≤ n with p + 2 also prime.
**Role.** The quantity M5 bounds; the coefficient sequence Abel summation transforms in M6.
**Proof idea.** Definition via `Nat.count`; monotonicity is a one-liner.
**Lean.** `twinPrimeCounting`, `twinPrimeCounting_monotone` (Salt/Brun.lean)
**Status.** ✅ M0 scaffold, 2026-07-06 (Fable-tier commit).
**Difficulty.** predicted A, actual A.

#### N0.2 — formal targets ✅
**Statement.** `TwinCountingBigO`: π₂(⌊x⌋) = O(x/(log x)²) at infinity. `BrunStatement`: the indicator-weighted series Σ 1/p over twin primes is summable.
**Role.** The track's two contracts: M5 proves the first, M6 the second. Stated as `Prop`s so `main` stays sorry-free until they become theorems.
**Proof idea.** Definitions; no proof content.
**Lean.** `TwinCountingBigO`, `BrunStatement` (Salt/Brun.lean)
**Status.** ✅ M0 scaffold, 2026-07-06.
**Difficulty.** predicted A, actual A.

### M1 — the fundamental theorem

#### N1.1 — truncated optimal weights 🔴
**Statement.** Define the Selberg weight sequence w, supported on {d ∣ P, d² ≤ y}, and prove w 1 = 1.
**Role.** The candidate weights fed to mathlib's Λ² machinery; N1.2 and N1.3 are properties of exactly this w.
**Proof idea (expected).** Adapt the reference definition (Mellendijk, cached): w d = ν(d)⁻¹ · g(d) · μ(d) · S⁻¹ · Σ_{m ∣ P, (dm)² ≤ y, (m,d)=1} g(m), with S the bounding sum Σ_{ℓ² ≤ y} g(ℓ). Then w 1 = 1 reduces to S ≠ 0, from positivity of `selbergTerms`.
**Lean.** — not started
**Status.** 🔴 open — **frontier** (class B, no dependencies).
**Difficulty.** predicted B.
**Notes.** First target under the port route (A1); attribution required.

#### N1.2 — weight size bound 🔴🔬
**Statement.** |w d| ≤ 1 for all d.
**Role.** Bounds the Λ² coefficients: |λ_d| ≤ 3^ω(d) in the error sum comes from this via the lcm expansion.
**Proof idea (expected).** Port of `selberg_bound_weights`: multiplicative telescoping comparing the constrained sum against S.
**Lean.** — not started
**Status.** 🔴 open; dep N1.1.
**Difficulty.** predicted C (port-assisted).

#### N1.3 — main-sum identity 🔴🔬
**Statement.** With the optimal w, mainSum(Λ²(w)) = 1/S where S = Σ_{ℓ ∣ P, ℓ² ≤ y} g(ℓ) — the G(√y) of the classical statement.
**Role.** *The* fundamental-theorem input: turns the diagonalized quadratic form into the 1/G main term. All of M5/M6 is downstream.
**Proof idea (expected).** Port of the diagonalisation + optimum evaluation; mathlib already has the diagonalization identity, the repo has the rest.
**Lean.** — not started
**Status.** 🔴 open; dep N1.1.
**Difficulty.** predicted C (port-assisted).

#### N1.4 — fundamental theorem 🔴🔬
**Statement.** siftedSum ≤ totalMass/S + Σ_{d ∣ P, d ≤ y} 3^ω(d)·|R_d|.
**Role.** The engine. N5.2 applies it with y = N^{1/5} to the twin sieve.
**Proof idea (expected).** Port of `selberg_bound_simple`: combine mathlib's Λ² upper bound with N1.2 (error coefficients) and N1.3 (main term).
**Lean.** — not started
**Status.** 🔴 open; deps N1.2, N1.3.
**Difficulty.** predicted C (port-assisted).
**Notes.** Check for in-flight mathlib PRs before porting (A3).

### M2 — twin instantiation

#### N2.1 — solution density ρ ✅
**Statement.** ρ(d) counts residues n mod d with n(n+2) ≡ 0; ρ(0) = 0.
**Role.** The local density whose ratio ρ(d)/d is the sieve's ν; every M2 statement is about ρ.
**Proof idea.** `Finset.filter` count over `ZMod d`; an unfolding lemma for d ≠ 0; a nat-valued root-set (`Rnat`, via `ZMod.val`) for counting arguments.
**Lean.** `rho`, `rho_pos`, `Rnat`, `Rnat_card`, `dvd_iff_mem_Rnat` (Salt/Brun/M2.lean)
**Status.** ✅ 2026-07-07 (Haiku, 1 attempt; definition refactored by Sonnet during N2.3; the `Rnat` machinery was added by Sonnet during the N2.2/N2.4 sessions).
**Difficulty.** predicted A, actual A — but the original pattern-match definition caused instance-defeq pain downstream; see flags 2026-07-07 N2.3.
**Notes.** `rho_pos` is an unfolding lemma, not positivity — rename candidate.

#### N2.2 — ρ is multiplicative ✅
**Statement.** ρ(mn) = ρ(m)·ρ(n) for coprime nonzero m, n.
**Role.** Makes ν multiplicative (a `BoundingSieve` field); with N2.3 it pins ρ on all squarefree d.
**Proof idea.** CRT bijection between root sets, via `Nat.chineseRemainder` and `Nat.ModEq` congruence arithmetic (three-part `Finset.card_bij`).
**Lean.** `rho_mul_of_coprime` (Salt/Brun/M2.lean)
**Status.** ✅ 2026-07-07 (Sonnet, 1 attempt).
**Difficulty.** predicted B, actual B.
**Notes.** Took `Nat.chineseRemainder` directly instead of the blueprint-suggested `ZMod.chineseRemainder` ring equivalence — unpacking the latter looked worse. Flags 2026-07-07 N2.2.

#### N2.3 — ρ at primes ✅
**Statement.** ρ(2) = 1; ρ(p) = 2 for every odd prime p.
**Role.** The prime-level values behind 0 < ν(p) < 1 (N2.6) and ρ ≤ 2^ω (N2.7).
**Proof idea.** In the field ZMod p, n(n+2) = 0 ⟺ n ∈ {0, −2}; the two roots coincide mod 2 and are distinct for odd p (else p ∣ 2).
**Lean.** `rho_two`, `rho_odd_prime`, `sol_set` (Salt/Brun/M2.lean)
**Status.** ✅ 2026-07-07 (Sonnet, 1 attempt plus a definitional refactor of ρ).
**Difficulty.** predicted B, actual B with an unplanned instance-defeq detour (flags 2026-07-07 N2.3).

#### N2.4 — progression count bound ✅
**Statement.** For d ≥ 1, the count of n ∈ [1, N] with d ∣ n(n+2) differs from N·ρ(d)/d by at most ρ(d).
**Role.** Cashes out "ρ(d)/d is the right density": becomes the sieve remainder bound |R_d| ≤ ρ(d) (N2.7), consumed by the error sum N4.2.
**Proof idea.** Any d consecutive integers hit each residue class mod d exactly once; each full block contributes exactly ρ(d) solutions; telescope, bound the partial block trivially.
**Lean.** `progression_count_bound` (Salt/Brun/M2.lean), via the general `congCount_bound` (Salt/Brun/CongruenceCounting.lean)
**Status.** ✅ 2026-07-07 (Sonnet, several iterations).
**Difficulty.** predicted B, actual ~C — no mathlib support; required building a reusable block-decomposition module.
**Notes.** `CongruenceCounting.lean` is general-purpose and mathlib-worthy. Flags 2026-07-07 N2.4.

#### N2.5 — the support ✅
**Statement.** n ↦ n(n+2) is strictly monotone (hence injective); the image of [1, N] under it has exactly N elements.
**Role.** Legitimizes totalMass = N; the injectivity powers every sum-over-support computation (`multSum`, `siftedSum`).
**Proof idea.** Nat inequality chain for monotonicity; `card_image_of_injective` for the count.
**Lean.** `twinProd_strictMono` (Salt/Brun/M2.lean); `Salt.TwinSieve.twinProd_injective`, `Salt.TwinSieve.sieve_support_card` (Salt/Brun/Sieve.lean)
**Status.** ✅ strictMono 2026-07-07 (Haiku); card = N landed inside the N2.6 session (Opus).
**Difficulty.** predicted A, actual A.
**Notes.** The card=N half was discharged retroactively during N2.6 — the node quietly spanned two sessions.

#### N2.6 — the BoundingSieve instance ✅
**Statement.** A mathlib `BoundingSieve` sifting {n(n+2) : n ∈ [1, N]} by the primes dividing a squarefree parameter P: ν(d) = ρ(d)/d multiplicative with 0 < ν(p) < 1 at every prime, unit weights, totalMass = N.
**Role.** The bridge into mathlib's Selberg machinery; M1's port, N3.1, and N5.1 all speak through this instance.
**Proof idea.** ν(p) ∈ (0,1) holds at *every* prime unconditionally (1/2 at 2; 2/p ≤ 2/3 at odd p), so P needs only squarefreeness; multiplicativity is N2.2; the sieve level enters only as the parameter P.
**Lean.** `Salt.TwinSieve.sieve`, `Salt.TwinSieve.nu`, `Salt.TwinSieve.nu_mult`, `Salt.TwinSieve.nu_pos_of_prime`, `Salt.TwinSieve.nu_lt_one_of_prime`, `Salt.TwinSieve.sieve_multSum`, `Salt.TwinSieve.sieve_rem` (Salt/Brun/Sieve.lean)
**Status.** ✅ 2026-07-07 (Opus, 1 attempt).
**Difficulty.** predicted B; Sonnet declined as C; actual B-at-Opus — the feared "choose a level z" design decision evaporated (z is just P's parameterization).
**Notes.** Connecting lemmas `sieve_multSum`/`sieve_rem` tie the abstract sieve to N2.4's concrete counts. Flags 2026-07-07 N2.6.

#### N2.7 — remainder and density bounds ✅
**Statement.** For squarefree d: |R_d| ≤ ρ(d) and ρ(d) ≤ 2^ω(d). (The first half is proved under the weaker hypothesis d ≠ 0.)
**Role.** Feeds N4.2: each error term is controlled by 2^ω, which N4.1 then absorbs into d³.
**Proof idea.** First half is N2.4 restated through the direct definition of `rem` (the N2.6 lemma `sieve_rem` separately identifies that with the sieve's remainder); second half is strong induction peeling one prime factor via N2.2 + N2.3.
**Lean.** `rem_abs_le`, `rho_squarefree_le`, `omega_mul_coprime`, `omega_prime` (Salt/Brun/M2.lean)
**Status.** ✅ 2026-07-07 (Sonnet).
**Difficulty.** predicted B, actual B.
**Notes.** The "part 1 needs a sieve instance" worry was dissolved by defining `rem` directly (see N4.2).

### M3 — main term, Mertens-free

#### N3.1 — selbergTerms at primes ✅
**Statement.** g(p) = ν(p)/(1 − ν(p)); explicitly g(2) = 1 and g(p) ≥ 2/p for odd p. (The exact value at odd p is 2/(p−2); only the inequality is kernel-checked.)
**Role.** The per-prime lower bounds that make G(z) large — the inputs N3.2 expands.
**Proof idea.** `selbergTerms_apply` at a prime has a singleton primeFactors product; then field arithmetic.
**Lean.** `Salt.TwinSieve.selbergTerms_prime`, `Salt.TwinSieve.selbergTerms_two`, `Salt.TwinSieve.selbergTerms_odd_prime_ge` (Salt/Brun/Sieve.lean)
**Status.** ✅ 2026-07-07 (Opus, 1 attempt).
**Difficulty.** predicted A, actual A.

#### N3.2 — geometric expansion 🔴
**Statement.** G(z) ≥ Σ_{m < z, m odd} ν*(m), where ν*(∏p^a) = ∏ν(p)^a — group m by radical and expand each (1−ν(p))⁻¹ as a finite geometric truncation.
**Role.** Converts G (supported on squarefree ℓ ∣ P) into a sum over *all* odd m < z, where the τ machinery (N3.3–N3.5) applies.
**Proof idea (expected).** Each squarefree ℓ ∣ P contributes g(ℓ) = ν(ℓ)·∏_{p∣ℓ}(1−ν(p))⁻¹ ≥ Σ_{rad(m)=ℓ, m<z} ν*(m); sum over ℓ. Careful radical/truncation bookkeeping; needs P to contain the odd primes below z (an N5.2 instantiation detail).
**Lean.** — not started
**Status.** 🔴 open — **frontier** (dep N3.1 ✅). The hardest remaining non-port node.
**Difficulty.** predicted C.
**Notes.** Fallback A4 (squarefree-part decomposition) if radical grouping stalls. See R2.

#### N3.3 — τ ≤ 2^Ω 🟡
**Statement.** τ(m) ≤ 2^Ω(m) for m ≠ 0; hence ν*(m) ≥ τ(m)/m for odd m.
**Role.** Bounds ν*(m) below by τ(m)/m — the summand N3.4 handles. (For odd m, ν*(m) is exactly 2^Ω(m)/m, so the two halves chain.)
**Proof idea.** τ(∏p^a) = ∏(a+1) ≤ ∏2^a termwise. Second half is a near-one-liner once ν* exists (N3.2).
**Lean.** `card_divisors_le_two_pow_cardFactors` (Salt/Brun/M3.lean)
**Status.** 🟡 partial — first half ✅ 2026-07-07 (Sonnet); second half waits on N3.2's ν*.
**Difficulty.** predicted B, actual B (first half).

#### N3.4 — divisor pairing ✅
**Statement.** Σ_{m<z, odd} τ(m)/m ≥ (Σ_{a<√z, odd} 1/a)².
**Role.** Converts the τ-sum into a squared harmonic sum — the source of the (log z)² growth.
**Proof idea.** Expand τ(m)/m over divisor pairs (m, d); inject T × T ∋ (a,b) ↦ (ab, a) into the pairs; compare nonnegative sums over the subset.
**Lean.** `N3_4`, `divSum_ge_sq`, `divSum`, `divPairs`, `divSum_eq_sum_divPairs` (Salt/Brun/M3.lean)
**Status.** ✅ 2026-07-07 (Sonnet, several iterations).
**Difficulty.** predicted B, actual ~C — "hardest of the self-contained B nodes" (flags 2026-07-07 N3.4).
**Notes.** `divSum_ge_sq` is general (any S ⊇ T·T with 0 ∉ T); rename `N3_4` → descriptive candidate.

#### N3.5 — odd harmonic lower bound ✅
**Statement.** Σ_{a≤t, odd} 1/a ≥ (log t)/2 − C with the explicit constant C = (1 − log 2)/2.
**Role.** Feeds N3.4's square: ((log √z)/2 − C)² ≳ (log z)²/16.
**Proof idea.** Odd sum = H_t − ½·H_{t/2}; mathlib's `log(n+1) ≤ H_n ≤ 1 + log n`; explicit-constant arithmetic.
**Lean.** `oddHarmonicSum_ge`, `oddHarmonicSum`, `oddHarmonicSum_eq`, `even_sum_eq_half_harmonic` (Salt/Brun/M3.lean)
**Status.** ✅ 2026-07-07 (Sonnet).
**Difficulty.** predicted B, actual B.
**Notes.** t = 1 is a *real* edge case (nat division + `log 0 = 0` junk value makes the general argument false there) — split off, not smoothed over. Flags 2026-07-07 N3.5.

#### N3.6 — the G lower bound 🔴
**Statement.** ∃ c₀ > 0 and z₀ such that G(z) ≥ c₀·(log z)² for all z ≥ z₀.
**Role.** The assembled main-term bound that N5.2 divides by.
**Proof idea (expected).** Chain N3.2 → N3.3 → N3.4 → N3.5 and collect the explicit constants.
**Lean.** — not started
**Status.** 🔴 open; blocked on N3.2 (N3.4/N3.5 ready; N3.3's second half also waits on N3.2).
**Difficulty.** predicted B.

### M4 — error term

#### N4.1 — 6^ω ≤ d³ ✅
**Statement.** For squarefree d, 6^ω(d) ≤ d³.
**Role.** Absorbs the 3^ω·2^ω error coefficients into a polynomial — this is what makes the crude error design (§2) work without divisor asymptotics.
**Proof idea.** 6 ≤ p³ for every prime p; multiply over primeFactors, whose product is d by squarefreeness.
**Lean.** `six_pow_omega_le_d_cubed`, `omega` (Salt/Brun/M4.lean)
**Status.** ✅ 2026-07-07 (Sonnet, 1 attempt, after a Haiku tier-flag).
**Difficulty.** predicted A, actual B — the project's first cascade escalation; needed the squarefree product API. Flags 2026-07-07 N4.1.

#### N4.2 — error sum ≤ y⁴ ✅
**Statement.** Σ_{d<y, squarefree} 3^ω(d)·|R_d| ≤ y⁴.
**Role.** The fundamental theorem's error term, instantiated: y = N^{1/5} makes it N^{4/5}, negligible in N5.2.
**Proof idea.** Termwise 3^ω·|R| ≤ 3^ω·ρ ≤ 6^ω ≤ d³ (N2.7 + N4.1); then Σ_{d<y} d³ ≤ y·y³.
**Lean.** `N4_2`, `rem`, `rem_abs_le`, `sum_cube_le_pow4` (Salt/Brun/M2.lean)
**Status.** ✅ 2026-07-07 (Sonnet, 1 attempt).
**Difficulty.** predicted A, actual A/B.
**Notes.** Lives in M2.lean (import order). Defining `rem` directly — count minus N·ρ(d)/d — retroactively dissolved the "needs a sieve instance" concerns on N2.7/N4.1. Rename `N4_2` → descriptive candidate.

### M5 — assembly

#### N5.1 — twins are sifted ✅
**Statement.** If P is squarefree and every prime factor of P is ≤ z, each twin-prime leader p ∈ (z, N] has p(p+2) coprime to P; hence the count of such leaders is ≤ siftedSum.
**Role.** The final bridge from sieve output back to π₂: π₂(N) ≤ z + siftedSum + O(1).
**Proof idea.** The only primes dividing p(p+2) are p and p+2, both > z; coprimality follows prime-by-prime; then inject into the sifted set.
**Lean.** `Salt.TwinSieve.twin_count_le_siftedSum`, `Salt.TwinSieve.twin_subset_coprime`, `Salt.TwinSieve.coprime_twinProd`, `Salt.TwinSieve.sieve_siftedSum` (Salt/Brun/Sieve.lean)
**Status.** ✅ 2026-07-07 (Opus, 1 attempt).
**Difficulty.** predicted B, actual B.
**Notes.** P kept as a parameter with an "all prime factors ≤ z" hypothesis — same z-deferral that de-fanged N2.6.

#### N5.2 — the counting bound 🔴
**Statement.** π₂(N) ≤ N/S + N^{4/5} + N^{1/10} + O(1), by applying N1.4 with y = N^{1/5}, z = √y, P = the primorial of z; S ≥ G(N^{1/10}) since g > 0, so N3.6's lower bound applies.
**Role.** Instantiates the whole machine; N5.3 absorbs the lower-order terms.
**Proof idea (expected).** Specialize N1.4 to the N2.6 instance; bound its error by N4.2, its sifted sum below by N5.1; count twins ≤ z by z.
**Lean.** — not started
**Status.** 🔴 open; blocked on N1.4 and N3.6 (N2.6, N4.2, N5.1 ready).
**Difficulty.** predicted B.
**Notes.** Exponent slack: any θ < 1/4 works; 1/5 is comfort margin (R4). The repo's `BrunTitchmarsh.lean` is a worked template for this kind of assembly.

#### N5.3 — TwinCountingBigO 🔴
**Statement.** π₂(N) = O(N/(log N)²).
**Role.** The M5 contract; the Big-O input to Abel summation.
**Proof idea (expected).** Divide N5.2 by N3.6's bound; absorb N^{4/5}, N^{1/10}, O(1) using `isLittleO_log_rpow_rpow_atTop`; the ⌊x⌋₊ idiom per Chebyshev.lean.
**Lean.** — not started
**Status.** 🔴 open; blocked on N5.2.
**Difficulty.** predicted B.

### M6 — summability

#### N6.1 — integrability at infinity ✅
**Statement.** t ↦ 1/(t·(log t)²) is integrable on a neighborhood of +∞.
**Role.** Convergence of the integral side of Abel summation (N6.2).
**Proof idea.** The antiderivative −1/log t is monotone with finite limit at ∞; `integrableOn_Ioi_deriv_of_nonneg'` does the rest — no substitution needed.
**Lean.** `integrableAtFilter_inv_id_mul_log_sq` (Salt/Brun/M6.lean)
**Status.** ✅ 2026-07-07 (Opus, 1 attempt, after a Sonnet tier-flag).
**Difficulty.** predicted B, actual B-at-Opus — the flagged "hard substitution" was a phantom; second cascade escalation. Flags 2026-07-07 N6.1.

#### N6.2 — BrunStatement 🔴
**Statement.** The sum of reciprocals of twin primes converges.
**Role.** The theorem. The track ends here (N6.3 is garnish).
**Proof idea (expected).** `summable_mul_of_bigO_atTop` with c = twin indicator and f = 1/·; N5.3 supplies the Big-O, N6.1 the integrability; glue `twinPrimeCounting` to the indicator sum (watch R5).
**Lean.** — not started
**Status.** 🔴 open; blocked on N5.3 (N6.1 ready).
**Difficulty.** predicted B.

#### N6.3 — Brun's constant 🔴
**Statement.** Define brunConstant as the value of the convergent series and prove its positivity.
**Role.** Bonus; makes the result quotable as a number.
**Proof idea (expected).** `tsum` of a summable nonneg sequence with a positive term (p = 3).
**Lean.** — not started
**Status.** 🔴 open; blocked on N6.2.
**Difficulty.** predicted A.
