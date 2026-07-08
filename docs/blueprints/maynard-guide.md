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

*Updated: 2026-07-07 (Opus, after Wave 1).*

- **State**: 15 of ~33 nodes done. M0, M1, N2.0, N3.1, and **Wave 1**
  (N2.1, N2.6, N2.7, N3.2, N3.5, N6.1) all proved, sorry-free, axiom-
  audited. The analytic bottleneck (N3.2, Mertens' 2nd upper — absent
  from mathlib, built from Chebyshev + von Mangoldt + Abel) is DONE.
- **Frontier** (deps met): **N2.2** (λ from y), **N3.4** (Rankin
  bound, deps N3.2 ✅), **N4.1** (congruence count, deps N2.1/N2.7 ✅).
- **Next**: Wave 2 (N2.2, N3.4, N4.1), then the N2.4/N2.5 k-dim
  diagonalization keystones and the M4/M5 spine (N4.2–N4.4, N5.1–N5.5),
  then M6 ratio (N6.2/N6.3) and M7 assembly (N7.1–N7.4).
- **Blockers**: none — every remaining node's deps are proved or in
  the next wave.
- **Strategic line**: Wave 1 retired the biggest single risk (Mertens)
  and confirmed the frozen design executes cleanly at scale — six
  independent nodes, all first-pass, one of them (N3.2) genuinely
  C-grade analytic NT. The hard remaining keystones are the k-dimensional
  diagonalizations (N2.4/N2.5) and the S₂-lower assembly (N5.5); the
  frozen statements and the 1-dim `SelbergPort` template de-risk them,
  but they are the true test of the track.

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

### M2/M3/M6 — Wave 1 (proved 2026-07-07, Opus; 6-node parallel fan-out)

#### N2.1 — the k-dim index set 𝒟 ✅
**Statement.** `kSieveIndex k R W`: the Finset of `r : Fin k → ℕ` of pairwise-coprime squarefrees, each coprime to `W`, with `∏ᵢ rᵢ < R`; `mem_iff` + per-coordinate `rᵢ < R`, `0 < rᵢ`.
**Role.** The index set every M2/M4/M5 sum ranges over.
**Proof idea.** Filter of `piFinset (range R)`; the reverse `mem_iff` re-derives `rᵢ < R` from `rᵢ ≤ ∏ⱼrⱼ < R` (`single_le_prod'`, factors `≥ 1` by squarefree-positivity).
**Lean.** `Salt.Maynard.kSieveIndex`, `mem_kSieveIndex_iff`, `kSieveIndex_coord_lt`, `kSieveIndex_coord_pos` (Salt/Maynard/KSieve.lean)
**Status.** ✅ 2026-07-07 (Opus, workflow + driver third-pass).
**Difficulty.** predicted B, actual B.

#### N2.6 — g/φ comparison ✅
**Statement.** `gMult r = ∏_{p|r}(p−2)`; for squarefree `r` with all prime factors ≥ 3: `g(r) ≤ φ(r)` and `φ(r)³ ≤ g(r)·r²` (real-valued).
**Role.** Restores literal-A₁ domination in the S₂ non-m coordinates (N5.5), preserving the D2 symbolic cancellation.
**Proof idea.** Push `φ, r, g` to single `∏ p ∈ primeFactors` products; `Finset.prod_le_prod` termwise, per-prime `(p−1)³ ≤ (p−2)p²` by `nlinarith` given `3 ≤ p`.
**Lean.** `Salt.Maynard.gMult`, `gMult_le_totient`, `totient_cubed_le_gMult_mul` (Salt/Maynard/GFunction.lean)
**Status.** ✅ 2026-07-07 (Opus, workflow + driver third-pass).
**Difficulty.** predicted A, actual A.

#### N2.7 — congruence compatibility ✅
**Statement.** Every prime factor of anything coprime to `W k` exceeds `D₀ k`; hence for `i ≠ j` no prime `> D₀ k` divides both `n+hSeq k i` and `n+hSeq k j` (it would divide the nonzero difference `≤ D₀ k`).
**Role.** The cross-collision-pairs contribute 0 (N4.4/N5.1).
**Proof idea.** `Nat.Prime.dvd_primorial_iff` for the first; ℤ-subtraction + `hSeq_injective`/`hSeq_le_D₀` + `Int.le_of_dvd` for the second.
**Lean.** `Salt.Maynard.D₀_lt_of_prime_dvd_coprime`, `not_common_prime_cross` (Salt/Maynard/Compat.lean)
**Status.** ✅ 2026-07-07 (Opus, workflow + driver third-pass).
**Difficulty.** predicted B, actual B.
**Notes.** `not_common_prime_cross`'s `p.Prime` hypothesis is unused (the collision is ruled out by size alone) — kept per iron rule 1, with a harmless linter-satisfier line.

#### N3.2 — Mertens' 2nd theorem, upper bound ✅
**Statement.** `Σ_{p ≤ n} 1/p ≤ log log n + C` and the `1/(p−1)` corollary — with leading coefficient **exactly 1** on log log.
**Role.** The analytic input to N3.4 (Rankin bound → N5.2 EH consumption). Mathlib has no Mertens; this builds it.
**Proof idea.** Divisor swap `Σ_{n≤N} log n = Σ_d Λ(d)⌊N/d⌋` (`vonMangoldt_sum`); `⌊N/d⌋ ≥ N/d−1` + Chebyshev `psi_le` ⇒ `Σ_{p≤N}(log p)/p ≤ log N + c` (Mertens 1st upper); then Abel summation (`sum_mul_eq_sub_integral_mul₁`) against `1/log t`, evaluating `∫1/(t log t) = log log` and `∫1/(t log²t) = −1/log t` by FTC.
**Lean.** `Salt.Maynard.sum_inv_prime_le`, `sum_inv_prime_sub_one_le`, `sum_log_div_prime_le`, `integral_inv_tlog`, `integral_inv_tlogsq` (Salt/Maynard/Mertens.lean)
**Status.** ✅ 2026-07-07 (Opus, workflow at high effort + driver crux-read of the two integrals and the Abel assembly). The single hardest node landed to date — the track's analytic bottleneck, absent from mathlib.
**Difficulty.** predicted B, actual **C** (genuine multi-step analytic NT from scratch).
**Notes.** The implementer caught a flaw in the driver's brief: the `1/(p−1) ≤ 2/p` corollary route gives coefficient 2, which fails the stated bound — replaced by a `1/(p−1) = 1/p + 1/(p(p−1))` telescoping bound keeping coefficient 1, without altering the statement.

#### N3.5 — Chebyshev interval ✅
**Statement.** `∃ c > 0, N₀, ∀ N ≥ N₀, c·N/log N ≤ π(64N) − π(N)`.
**Role.** The prime-supply lower bound `Δπ ≥ cN/log N` for S₂ (N5.5).
**Proof idea.** `Chebyshev.pi_ge`/`pi_le_log4_mul_div`; the leading coefficient is `28·log 2 ≈ 19.4` vs required `1`; the `√N` and `log(64N+1)` lower-order terms killed by two `Tendsto …(𝓝 0)` lemmas; `nlinarith` with `Real.log_two_gt_d9`.
**Lean.** `Salt.Maynard.primes_in_interval_ge` (Salt/Maynard/ChebyshevInterval.lean)
**Status.** ✅ 2026-07-07 (Opus, workflow + driver third-pass).
**Difficulty.** predicted B, actual B. **Notes.** conspiracy is exactly at `K₀ = 2`; `64` clears it with margin `62 log 2`.

#### N6.1 — g-integral closed forms ✅
**Statement.** For `A > 0, T ≥ 0`: `∫₀^T 1/(1+Au) = log(1+AT)/A`, `∫₀^T 1/(1+Au)² = T/(1+AT)`, `∫₀^T u/(1+Au)² = (log(1+AT) − AT/(1+AT))/A²`, `∫₀^T u²/(1+Au)² ≤ T/A²`.
**Role.** The 1-dim calculus feeding the M6 ratio (N6.2).
**Proof idea.** FTC (`integral_eq_sub_of_hasDerivAt`) with explicit antiderivatives; the last is a pointwise `(u/(1+Au))² ≤ 1/A²` + `integral_mono_on`. `A, T` fully general.
**Lean.** `Salt.Maynard.integral_g`, `integral_g_sq`, `integral_u_g_sq`, `integral_u_sq_g_sq_le` (Salt/Maynard/GIntegrals.lean)
**Status.** ✅ 2026-07-07 (Opus, workflow + driver third-pass).
**Difficulty.** predicted B, actual B.

### M2/M3/M4/M5/M6/M7 — remaining nodes frozen (N2.0), not yet executed

Frozen statements in `docs/blueprints/maynard.md`. Frontier after Wave 1:
**N2.2** (λ from y), **N3.4** (Rankin bound, deps N3.2 ✅), **N4.1**
(congruence count, deps N2.1/N2.7 ✅). Then the N2.4/N2.5 diagonalization
keystones and the M4/M5 spine.
