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

*Updated: 2026-07-07 (Sonnet).*

- **State**: 7 of ~30 nodes proved (M0, M1 complete). Track opened today
  on branch `maynard`, immediately after Brun's theorem landed on `main`.
- **Probe result** (N3.1, dispatched in parallel with M0/M1): the μ²/φ
  atom's **lower bound landed with the exact constant** φ(B)/B (load-
  bearing outcome, confirmed). The **upper bound did not land exact or
  at 2×** — best achieved is 4×-lossy, plus a crude fallback. The clean
  route (a signed multiplicative convolution, `Σ h(d)/d = 1` via a
  `p`/`p²` cancellation miracle) is real but is its own C-difficulty
  node, not a byproduct of the elementary route tried. **This is new
  information the N2.0 design freeze must account for** — the blueprint
  scoping doc assumed the atom would be cheap in both directions.
- **Frontier** (open, all deps met): N2.0, the design freeze — but it is
  Fable/human-tier only, and should now explicitly decide whether the
  track needs the exact-constant μ²/φ upper bound (budget a dedicated
  C-node per the probe's recommendation) or can proceed with the 4×-lossy
  form (check whether the tensor-mains-are-exact argument in the
  blueprint's Design Decision 4 tolerates a 4× loss on this one
  ingredient — it enters the error side, not obviously the main side, so
  this may be fine, but that judgment call is exactly what N2.0 is for).
- **Next step**: a Fable/human session should read the full probe report
  (flags.md 2026-07-07 N3.1 entry) and open N2.0. M0/M1's remaining
  probe-independent neighbor, M1's tuple construction, is done; nothing
  else is unblocked until N2.0 freezes the M3-M6 statements.
- **Blockers**: N2.0 (design freeze, Fable-tier) gates all of M2-M6.
- **Strategic line**: the track's entry ramp (M0, M1) is solid and
  reused Brun-track muscle cleanly (CRT induction, primorial squarefree,
  the block-counting/harmonic idiom). The one real surprise so far is
  the μ²/φ atom's asymmetry — lower bounds came free, the exact upper
  bound needs real machinery. This is exactly the kind of fact the probe
  was for; better to learn it now, seven nodes in, than after M2-M6 are
  built against a wrong assumption.

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
constant is loose and k is huge (θ=1/2, k₀≈10⁶, comically large gap
bound); (2) the tuple is a *theorem* — H = the first k primes greater
than k, admissibility is two lines, not a `decide` certificate; (3) W is
a *fixed* primorial (k fixed ⇒ no log-log-log dance); (4) tensor-product
weights make every k-fold main term factor *exactly* into products of
1-dimensional sums — no per-variable approximation compounds as Cᵏ.
Decision 4's viability rests on the 1-dimensional atoms (M3) being clean;
**the N3.1 probe (§0) found the upper-bound atom is not as clean as
hoped** — this is exactly the kind of fact decision 4 needs re-examined
against, which is why N2.0 (Fable) comes next.

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

### M2-M7 — not yet opened

Blocked on N2.0 (design freeze, Fable/human-tier), itself informed by the
N3.1 probe result (§0). See `docs/blueprints/maynard.md` for the full
DAG and `docs/blueprints/flags.md` for the probe's detailed technical
report.
