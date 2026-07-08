# Maynard's theorem (conditional) — reader's guide

<!--
MAINTENANCE RULES (contract; mirrors brun-guide.md's — see CLAUDE.md
workflow step 5 + iron rule 5)

Who may edit what:
  - All prose sections (§1-§5) and every card's **Statement.** / **Role.**
    field: Fable/human sessions ONLY. These are the immutable shadow of the
    blueprint (`docs/blueprints/maynard.md`) statements (iron rule 1
    applies to them). NOTE: this guide's §1/§2 prose and every card's
    Statement/Role field below were TRANSCRIBED VERBATIM from
    `maynard.md` (already Fable-authored at blueprint ratification) by a
    Sonnet session creating this file for the first time — no new claims
    were composed; see the 2026-07-07 M0/M1 flags.md entry.
  - Card volatile fields (**Proof idea. Lean. Status. Difficulty. Notes.**),
    Mermaid status classes/emoji, and the §0 frontier list: any tier, as
    part of landing or flagging a node (same commit as the proof —
    workflow step 5).
  - The §0 strategic line: Fable/human only.
  - The N2.0 design-freeze card (once opened) and anything it amends in
    M3-M6 statements: Fable/human only (blueprint-designated exception).

Status tokens (identical to brun-guide.md):
  ✅ proved (sorry-free, axiom-audited)   🟡 partial (Status line says which part)
  🔴 open                                 ⛔ tier-blocked (attempted; see flags)
  🔬 research-keystone annotation (may combine with 🔴/⛔)

Card grammar (parsed by scripts/blueprint_lint.py once generalized —
NOT yet wired up for this file; see flags.md 2026-07-07 note):
  #### N<x>.<y> — <short name> <status token>
  **Statement.** <prose; immutable>
  **Role.** <prose; immutable>
  **Proof idea.** <actual if proved, "(expected)" if open>
  **Lean.** `fully.qualified.name` (file); ... | — not started
  **Status.** <token> <detail; date; tier, attempts>
  **Difficulty.** predicted <class>[, actual <assessment>]
  **Notes.** <optional>

Green lint = "not mechanically stale", never "the prose is true".
-->

## 0. Briefing

*Updated: 2026-07-07 (Fable, at the N2.0 freeze).*

- **State**: 9 of ~33 nodes done (M0, M1, N3.1 probe, N2.0 design
  freeze). The design is FROZEN: all M2–M6 statements are now fixed in
  `maynard.md` (amended at N2.0; iron rule 1 applies to them from here).
- **The freeze in one line**: the probe's rungs suffice (no
  exact-constant convolution node needed); mains cancel symbolically
  with exactly one lossy 4× in the ratio; three r-averaged poly(k)/D₀
  correction families; empirical-ratio-centered overshoot; window
  [N, 64N); D₀ bumped to max(k³, max H) in Lean.
- **The freeze was adversarially reviewed** (three-reviewer panel, all
  REPAIRABLE→repaired): the panel caught a real error in the draft
  (S₂ diagonalizes with g(p) = p−2 denominators, not φ — φ is
  unprovable) plus eight repairs, all incorporated. See flags.md
  2026-07-07 N2.0.
- **Frontier** (open, all deps met, parallelizable): N2.1, N2.2, N2.6
  (A!), N2.7, N3.2, N3.4, N3.5, N6.1 — eight nodes, mostly B. Then
  N2.3–N2.5, N3.3 unlock the M4/M5 spine.
- **Blockers**: none. The critical path runs N2.4/N2.5 → N5.3/N5.5
  (the contraction and S₂-lower, hardest nodes in the track).
- **Strategic line**: the design risk is retired the same way Brun's
  was — by probe + adversarial review BEFORE building. What remains is
  execution: ~24 nodes, C-heavy in M4/M5, every statement now frozen
  and reviewed. The k-dim diagonalization (N2.4/N2.5) is the next
  keystone and has the 1-dim `SelbergPort` proofs as its template.

## 1. Big picture

*(Transcribed from `docs/blueprints/maynard.md`'s header, unchanged.)*

**Target.** `Salt/Maynard.lean`, `BoundedGapsFromEH`:
```
EH (1/2) → ∃ C, ∀ N, ∃ p q, N < p ∧ N < q ∧ p ≠ q ∧
  p.Prime ∧ q.Prime ∧ (q : ℤ) - p ∈ Set.Icc (-(C:ℤ)) C
```
where `EH θ` states the primes have level of distribution θ (a
Bombieri–Vinogradov-shaped hypothesis; BV itself, unformalized anywhere,
would instantiate θ = 1/2). Maynard's theorem, in load-bearing
conditional form. **No load-bearing formalization exists in any
assistant** (recon 2026-07). Second rung of the ladder; the machinery
(multidimensional Selberg sieve) is shared by every later rung toward
TPC.

## 2. The route, and the locked design decisions

*(Transcribed from `maynard.md`'s "Route" section, unchanged.)*

Fix an admissible k-tuple H. Weight each n ≡ ν₀ (mod W), N ≤ n < 2N by
w(n) = (Σ_{d : dᵢ ∣ n+hᵢ} λ_d)². Compare S₂ = Σ_n (#primes among
n+hᵢ)·w(n) against S₁ = Σ_n w(n): if S₂ > S₁ for all large N, some n in
every window has ≥ 2 primes among n+hᵢ. S₁ needs only counting; S₂'s
error consumes `EH`. The main-term ratio grows like log k, so a large
concrete k buys unlimited slack.

**Four locked design decisions** (full text in `maynard.md`): (1) every
constant is loose and k is huge (θ=1/2; post-freeze the honest chain
puts log k₀ in the thousands — the gap bound is astronomical by design,
M6 handles k₀ abstractly); (2) the tuple is a *theorem* — H = the first k primes greater
than k, admissibility is two lines, not a `decide` certificate; (3) W is
a *fixed* primorial (k fixed ⇒ no log-log-log dance); (4) tensor-product
weights make every k-fold main term factor *exactly* into products of
1-dimensional sums — no per-variable approximation compounds as Cᵏ.
Decision 4's viability rested on the 1-dimensional atoms (M3) being
clean; the N3.1 probe found the upper-bound atom is only 4×-lossy, and
the N2.0 freeze (now done — see its card) re-examined decision 4 against
that fact and repaired it: the cancellation is *symbolic* (same abstract
A₁ in numerator and denominator), so exactly one lossy 4 survives into
the ratio, absorbed by k. The panel-corrected fine print (g(p) = p−2
denominators in S₂, β(r) factors, three r-averaged correction families,
empirical-centered overshoot) is in `maynard.md`'s freeze section.

## 3. Node catalog

### M0 — statements & the hypothesis

#### N0.1 — π(x;q,a) ✅
**Statement.** `primesCount x q a`, the number of primes `p ≤ x` with
`p ≡ a (mod q)`; monotone in `x`.
**Role.** The counting function every later milestone's error terms are
stated against.
**Proof idea.** `Nat.count` over a residue-restricted predicate on
`range(x+1)`; monotonicity mirrors Brun's `twinPrimeCounting_monotone`
proof shape exactly.
**Lean.** `primesCount`, `primesCount_monotone`, `primesCount_one_zero` (Salt/Maynard.lean)
**Status.** ✅ 2026-07-07 (Sonnet, delegated implement+verify workflow, driver third-pass).
**Difficulty.** predicted A, actual A.

#### N0.2 — the trivial bound ✅
**Statement.** `π(x;q,a) ≤ x/q + 1` (at most one prime per residue class
per block of length `q`).
**Role.** The unconditional factor multiplying the EH-controlled error
in later Cauchy–Schwarz steps (M5).
**Proof idea.** Injectivity of `n ↦ n/q` on `{n < x+1 : n≡a (q)}` lands
the filtered Finset's card inside `range(x/q+1)`, via
`Finset.card_le_card_of_injOn`. The `q ≠ 0` hypothesis turned out unused
— the argument holds unconditionally.
**Lean.** `primesCount_le` (Salt/Maynard.lean)
**Status.** ✅ 2026-07-07 (Sonnet, delegated workflow, driver third-pass).
**Difficulty.** predicted B, actual A/B (simpler than expected — no case
split on residue alignment was needed).

#### N0.3 — the `EH θ` hypothesis and targets ✅
**Statement.** `EH θ`: for every `A > 0`, the sum over moduli `q ≤ x^θ`
of the maximal discrepancy `|π(x;q,a) − π(x)/φ(q)|` over reduced
residues `a`, is `O(x/(log x)^A)`. `EH` is antitone in `θ`.
`BoundedGapsFromEH := EH(1/2) → (the bounded-gaps conclusion)`.
**Role.** The single load-bearing hypothesis of the whole track; the
statement everything from M2 onward is built to consume (M5's Cauchy–
Schwarz step) or state around.
**Proof idea.** `EH`'s "max over residues" is encoded via `Finset.sup'`
over the reduced-residue Finset (nonempty since every `q ≥ 1` has a
coprime residue below it — `exists_coprime_lt`), factored through an
auxiliary total function `maxDiscrepancy` (handles `q=0` junk value
cleanly, never reached in the actual sum). `EH_antitone` follows from
`Finset.Icc` monotonicity in the upper bound (as `θ` shrinks, the summed
range shrinks) plus nonnegativity of every term.
**Lean.** `EH`, `maxDiscrepancy`, `exists_coprime_lt`, `EH_antitone`, `BoundedGapsFromEH` (Salt/Maynard.lean)
**Status.** ✅ 2026-07-07 (Sonnet, delegated workflow with an explicit
maximal-skepticism verify pass on this specific node given its
significance — checked for silent vacuity/triviality; confirmed
genuinely non-trivial: a crude block-counting bound alone gives only
`O(x log x)`, not `O(x/(log x)^A)` for arbitrary `A`, so `EH` encodes
real equidistribution content, not something free).
**Difficulty.** predicted B, actual B.
**Notes.** The faithful `Finset.sup'` encoding worked on the first
attempt (no fallback to an inlined-∀ alternative was needed).

### M1 — the admissible tuple

#### N1.1 — admissibility, definition ✅
**Statement.** `Admissible H`: for every prime `p`, some residue class
mod `p` is missed by every element of `H`.
**Role.** The property the concrete tuple `H k` (N1.2-N1.3) must satisfy
for the W-trick (N1.4) to find a valid `ν₀`.
**Proof idea.** Direct definition; `Admissible.mono` (subsets of
admissible tuples are admissible) is a one-line ∀-shrink.
**Lean.** `Admissible`, `Admissible.mono` (Salt/Maynard/Tuple.lean)
**Status.** ✅ 2026-07-07 (Sonnet, delegated workflow, driver third-pass).
**Difficulty.** predicted A, actual A.

#### N1.2 — the concrete tuple `H k` ✅
**Statement.** `H k` := the first `k` primes strictly greater than `k`
(via the increasing enumeration `Nat.nth Nat.Prime`, skipping past the
`Nat.count Nat.Prime (k+1)` primes that are `≤ k`). `card (H k) = k`;
every element is prime; every element is `> k`.
**Role.** The concrete admissible tuple the whole track instantiates
against — chosen so admissibility (N1.3) is a two-case argument instead
of a `decide` certificate.
**Proof idea.** `firstIdxAboveK k := Nat.count Nat.Prime (k+1)`; `H k :=
(range k).image (i ↦ nth Prime (firstIdxAboveK k + i))`. Card via
injectivity of `nth` (strict mono). The `> k` property is the one
genuinely fiddly step: contradiction via `count`/`nth` interplay
(`Nat.count_monotone`, `Nat.count_succ`, `Nat.count_nth_of_infinite`).
**Lean.** `firstIdxAboveK`, `H`, `H_card`, `H_prime`, `firstIdxAboveK_gt`, `H_gt_k` (Salt/Maynard/Tuple.lean)
**Status.** ✅ 2026-07-07 (Sonnet; the `> k` lemma was pre-validated by
the driving session in an isolated scratch file before delegation).
**Difficulty.** predicted B, actual B.
**Notes.** `push_neg` is deprecated in the pinned toolchain in favor of
`push Not` — same finding independently rediscovered here as in the
Brun track's N3.x nodes (different deprecation, same lesson: check
current tactic names before delegating).

#### N1.3 — `H k` is admissible ✅
**Statement.** `Admissible (H k)`.
**Role.** Feeds N1.4's `ν₀` construction.
**Proof idea.** Two cases on a prime `p`: `p ≤ k` — every element of
`H k` is a prime `> k ≥ p`, hence `≠ p`, hence never `≡ 0 (mod p)`
(residue witness `0`); `p > k` — pigeonhole, since `card (H k) = k < p =
card (ZMod p)`, the map `H k → ZMod p` isn't surjective, so some residue
is missed.
**Lean.** `H_admissible` (Salt/Maynard/Tuple.lean)
**Status.** ✅ 2026-07-07 (Sonnet, delegated workflow, driver third-pass — read the full proof, confirmed both cases are genuine, no gaps).
**Difficulty.** predicted B, actual B.

#### N1.4 — the W-trick: fixed modulus, `ν₀` exists ✅
**Statement.** `D₀ k := max k (sup (H k))`; `W k := primorial (D₀ k)`.
There is `ν₀` with `Nat.Coprime (ν₀ + h) (W k)` for every `h ∈ H k`.
**Role.** Fixes the single residue class `n ≡ ν₀ (mod W k)` the whole
sieve (M2 onward) restricts to, so every `n + h` (`h ∈ H k`) is coprime
to every prime `≤ D₀ k` from the start.
**Proof idea.** `W_squarefree` reproved locally (a 3-line induction,
deliberately not importing `Salt.Brun.M5Assembly` to avoid pulling in
the whole Brun sieve stack for one utility lemma). `exists_nu0`: for each
prime `p ∣ W k`, `H_admissible` supplies a residue to avoid; genuine
strong induction over the (finite) `Finset` of prime factors of `W k`,
combining one `Nat.chineseRemainder` step per prime via `Nat.ModEq`
bookkeeping (not the `ZMod.chineseRemainder` ring-equiv route — the
brief flagged that as a fallback, but the manual induction worked
directly).
**Lean.** `D₀`, `W`, `W_squarefree`, `exists_nu0` (Salt/Maynard/Tuple.lean)
**Status.** ✅ 2026-07-07 (Sonnet, delegated workflow, driver third-pass — read the full CRT induction, confirmed genuine and non-circular).
**Difficulty.** predicted B, actual B.
**Notes.** D₀ amended at the N2.0 freeze (2026-07-07, Fable): `max k (sup H)` → `max (k^3) (sup H)` — the k³ floor is load-bearing for every M4/M5 correction estimate; caught by the design-review panel; all M1 proofs were magnitude-agnostic, none broke.

### N2.0 — the design freeze ✅
**Statement.** Fix all parameters (K₀, R, g, A, T, f, y, D₀) and freeze the M3–M6 statements so that the N3.1 probe's landed rungs suffice.
**Role.** The designated Fable-tier amendment point for the whole track; after it, iron rule 1 applies to M2–M6 statements.
**Proof idea.** Paper design (tensor mains cancel symbolically; one lossy 4× in the ratio; three r-averaged correction families; empirical-centered overshoot) + a three-reviewer adversarial panel that caught one real error (S₂'s quadratic form needs g(p)=p−2 denominators, not φ) and eight repairs, all incorporated into the blueprint amendment.
**Lean.** — (design node; its Lean footprint is the D₀ amendment in Salt/Maynard/Tuple.lean and the frozen statements in maynard.md)
**Status.** ✅ 2026-07-07 (Fable; panel = 3 × effort-high adversarial reviewers, verdicts REPAIRABLE→repaired; full record in flags.md).
**Difficulty.** predicted D, actual D (the panel earned its cost: the draft freeze would have made N2.5 unprovable as stated).

### N3.1 — the μ²/φ atom (probe) ✅
**Statement.** `Σ_{r<x, squarefree, (r,B)=1} 1/φ(r)`: lower bound at the exact constant `(φ(B)/B)(log x − C_B)`; upper bounds at 4×-lossy and fallback quality.
**Role.** The single analytic atom all M3 weighted transfers partial-sum against; the probe that gated N2.0.
**Proof idea.** Lower: radical decomposition (n = rad(n)·m unique) + block-counting coprime harmonic bounds — `M3Expansion`'s technique verbatim. Upper: finite identity `r/φ(r) = Σ_{d∣r} 1/φ(d)`, divisorsAntidiagonal factorization, `d ≤ 2φ(d)²` tail. Exact-upper needs a signed-convolution identity — documented PORT-BLOCKER, deliberately NOT built (N2.0 D1).
**Lean.** `Salt.Maynard.phiAtom_lower`, `phiAtom_upper_lossy`, `phiAtom_upper_fallback`, `sqfCop`, `phiAtomSum` (Salt/Maynard/PhiAtom.lean)
**Status.** ✅ 2026-07-07 (delegated implement+verify workflow at effort-high; driver verification pass at the N2.0 session: build by module name, forbidden-token grep, crux read of `fiber_sum_le_inv_totient`).
**Difficulty.** predicted C, actual C (the upper-bound asymmetry was the probe's key finding).

### M2-M7 — statements frozen (N2.0), execution not yet started

All M2–M7 statements are frozen as of the N2.0 amendment — see
`docs/blueprints/maynard.md` (the freeze section + amended DAG tables)
and `docs/blueprints/flags.md` for the panel record. Frontier: N2.1,
N2.2, N2.6, N2.7, N3.2, N3.4, N3.5, N6.1.
