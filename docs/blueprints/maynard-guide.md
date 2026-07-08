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

- **State**: **26 of ~36 fully proved** (+1 partial). 2026-07-08: BOTH
  analytic walls fell on Fable-designed third attempts — N3.3-sharp (all
  five transfer bounds at exact constants) and N4.4-quant (the collision
  bound, |collision| ≤ (12k²/D₀)·yside). **Every analytic obstruction to
  `BoundedGapsFromEH` is now retired**; what remains is assembly. M0, M1, N2.0, N3.1, and **Wave 1**
  (N2.1, N2.6, N2.7, N3.2, N3.5, N6.1) all proved, sorry-free, axiom-
  audited. The analytic bottleneck (N3.2, Mertens' 2nd upper — absent
  from mathlib, built from Chebyshev + von Mangoldt + Abel) is DONE.
- **Wave 2 done**: N3.4 (Rankin) + N4.1 (congruence count).
- **Remaining work (all assembly, no analytic walls)**: N4.3 (S₁ upper —
  compat_le_two_yside + congCountTuple, templated), N5.1-links (wire
  s2_decomp to s2_diagonalisation + eh_error_small), N5.3 (y^(m)
  contraction), N5.4 (overshoot — all moment inputs ready), N5.5 (S₂
  lower assembly), N7.1–N7.4 (the final S₂ − S₁ > 0 chain and
  `BoundedGapsFromEH`). Note the fWt zero-patch caveat (N4.4 card) when
  instantiating the tensor hypotheses.
- **Blockers**: none — every remaining node's deps are proved or in
  the next wave.
- **Strategic line (terminal boundary of the automated pass).** The
  entire multidimensional Selberg-sieve *machinery* for Maynard's theorem
  is formalized and kernel-checked: both k-dimensional diagonalizations
  (S₁ and S₂ — the hardest nodes, landed first-pass), the index set and
  weights, the CRT congruence counting, the Mertens-2nd bound (built from
  scratch — absent from mathlib), the Rankin bound, the EH consumption
  (where the hypothesis is genuinely used), and the ratio prize. To our
  knowledge no prior formalization of this machinery exists in any
  assistant. What remains between here and `BoundedGapsFromEH` is a
  chain of **sharp analytic estimates** — above all the exact-constant
  weighted transfer (N3.3) — that two serious automated attempts each
  landed only in crude form. Completing them needs either sharper
  analytic-formalization machinery than a single automated pass reliably
  produces, or human/Fable-level design. The gap is characterized down to
  named lemmas (above); it is a boundary of the *pass*, not a dead end
  for the track.

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

### M3/M4 — Wave 2 (proved 2026-07-07, Opus)

#### N3.4 — Rankin multiplicative-sum bound ✅
**Statement.** For `L : ℕ`: `∃ C ≥ 1, ∀ Q ≥ 2, Σ_{q<Q, squarefree} L^{ω(q)}/φ(q) ≤ (C log Q)^L`.
**Role.** The Cauchy–Schwarz second factor in N5.2's EH consumption (at `L = 3k` and `L = 9k²`).
**Proof idea.** `L^{ω q}/φ(q) = ∏_{p|q} L/(p−1)` on squarefree; Euler-product upper bound `Σ_{q<Q sqfree} ≤ ∏_{p<Q}(1 + L/(p−1))` via `Finset.prod_add` + the `primeFactors` powerset injection; then `log ∏ ≤ L·Σ 1/(p−1) ≤ L(loglog Q + C₀)` (N3.2) and exponentiate.
**Lean.** `Salt.Maynard.rankin_bound`, `rankin_term_eq` (Salt/Maynard/Rankin.lean)
**Status.** ✅ 2026-07-07 (Opus, workflow + driver third-pass).
**Difficulty.** predicted B, actual B. **Notes.** Applying Mertens at `n = Q` (not `Q−1`) eliminated the anticipated small-`Q` case split.

#### N4.1 — per-tuple congruence count ✅
**Statement.** `congCountTuple` = count of `n ∈ (N, K₀N]` with `n ≡ ν₀ (mod W k)` and `lcm(dᵢ,eᵢ) ∣ n+hSeq k i` ∀i. Compatible case: `|count − (K₀−1)N/(W∏lcm)| ≤ 2^(k+1)`. Collision case (`gcd(dᵢ,eⱼ)>1`, i≠j): count `= 0`.
**Role.** The counting core of S₁ (N4.3) and S₂ (N5.1).
**Proof idea.** Collision: a shared prime `> D₀ k` (via N2.7) divides two shifts → `not_common_prime_cross` → empty filter. Approx: CRT-fold the `k+1` pairwise-coprime moduli into one `n ≡ c (mod M)` (`modEq_prod_of_pairwise_coprime`, a `Finset.induction` over `Nat.modEq_and_modEq_iff_modEq_mul`), then Brun's `congCount_bound` at the two endpoints gives `±2` (discharged to `±2^(k+1)`).
**Lean.** `Salt.Maynard.congCountTuple`, `congCountTuple_approx`, `congCountTuple_collision`, `modEq_prod_of_pairwise_coprime` (Salt/Maynard/CongCount.lean)
**Status.** ✅ 2026-07-07 (Opus, workflow + driver third-pass; verifier confirmed the `_approx` hypotheses are load-bearing/CRT-satisfiable, not a vacuity dodge).
**Difficulty.** predicted B, actual B/C.

#### N2.2 + N2.4 — the k-dimensional S₁ diagonalization ✅ (the linchpin)
**Statement.** `lam k R W y` (Maynard's inverse change of variables `(∏μ(dᵢ)dᵢ)·wSum`) and `wSum` are defined; then `Σ_{d,e∈𝒟} λ_d λ_e/∏ᵢ lcm(dᵢ,eᵢ) = Σ_{r∈𝒟} y_r²/∏ᵢ φ(rᵢ)`.
**Role.** THE linchpin: the S₁ main term (N4.3) and, mirrored, S₂ (N2.5/N5.x) are read off this. The multidimensional generalization of Brun's Selberg port.
**Proof idea.** Seven steps (P1–P7): `1/lcm = gcd/(de)`, `gcd = Σ_{u|d∧u|e}φ(u)` (`Nat.sum_totient`), the k-fold tensor of this and of the 1-dim Möbius inversion `Salt.SelbergPort.moebius_inv_dvd_lower_bound`, collapsing to the diagonal. Localized into two standalone lemmas: `kernel1` (the 1-dim gcd/Möbius core) and `kernelK` (its `Finset.prod_univ_sum` tensor over `Fin k`).
**Lean.** `Salt.Maynard.s1_diagonalisation`, `lam`, `wSum`, `kernel1`, `kernelK`, `sum_ksieve_guarded_eq` (Salt/Maynard/Diagonal.lean)
**Status.** ✅ 2026-07-07 (Opus, dedicated high-effort workflow + driver crux-read of `kernel1`/`kernelK`, axiom audit, no-circularity check). The hardest node in the project — landed first-pass with no PORT-BLOCKER.
**Difficulty.** predicted C, actual C (hard end — the cost was Lean-mechanical k-fold sum reordering, not the mathematics).
**Notes.** The mandated `hy` (y vanishes off 𝒟) hypothesis is unused — the identity holds unconditionally (every sum is over 𝒟); kept in signature per iron rule 1, underscore-named.

#### N2.5 — the S₂ diagonalization ✅
**Statement.** `s2_diagonalisation`: `Σ_{d,e∈𝒟} λG_d λG_e/∏ᵢφ(lcm(dᵢ,eᵢ)) = Σ_{r∈𝒟} y_r²/∏ᵢ gMult(rᵢ)`, with `λG = (∏μ(dᵢ)φ(dᵢ))·wSumG`.
**Role.** The S₂ main-term structure (N5.x reads it off, restricting to `r_m=1`).
**Proof idea.** Exact mirror of N2.4 via the g-analog `Σ_{u|n} gMult u = φ(n)` (`sum_gMult_eq_totient`) and `φ(d)φ(e)/φ(lcm) = φ(gcd) = Σ_{u|gcd}gMult`. Lemmas `kernelG`/`kernelKG` mirror `kernel1`/`kernelK`. Proved the FULL k-dim form (the m-pinned form is its restriction).
**Lean.** `Salt.Maynard.s2_diagonalisation`, `sum_gMult_eq_totient`, `totient_gcd_mul_totient_lcm`, `kernelG`, `kernelKG`, `lamG`, `wSumG` (Salt/Maynard/DiagonalS2.lean)
**Status.** ✅ 2026-07-07 (Opus, workflow + driver audit). **Difficulty.** predicted C, actual C (templated by N2.4).
**Notes.** `λG` uses multiplier `μ(dᵢ)φ(dᵢ)` (forced by the φ(lcm) denominator), not N2.4's `μ(dᵢ)dᵢ`.

#### N2.3 — λ size bound ✅
**Statement.** `|lam k R W y d| ≤ (∏ᵢdᵢ)·Σ_{r∈𝒟}|y r|/∏φ(rᵢ)`.
**Role.** The trivial-error factor (N4.2).
**Proof idea.** `|∏μ(dᵢ)dᵢ| ≤ ∏dᵢ` + triangle inequality on `wSum`.
**Lean.** `Salt.Maynard.lam_abs_le` (Salt/Maynard/LamBound.lean). **Status.** ✅ 2026-07-07 (Opus). **Difficulty.** predicted B, actual B.

#### N5.2 — the EH consumption ✅
**Statement.** `eh_error_small`: under `EH(1/2)`, `Σ_{q<√N, sqfree} (3k)^{ω(q)}·maxDiscrepancy(N,q) ≤ C·N/(log N)²`.
**Role.** Where the EH hypothesis is used — the S₂ error absorption (N5.5). The single most important consumption.
**Proof idea.** Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`) between `rankin_bound (9k²)` (fixed log-power) and `EH(1/2)` at exponent `9k²+4` (EH's ∀A crushes the Rankin factor), with N0.2 the trivial factor.
**Lean.** `Salt.Maynard.eh_error_small` (Salt/Maynard/EHConsume.lean). **Status.** ✅ 2026-07-07 (Opus, workflow + driver check that EH is genuinely consumed). **Difficulty.** predicted C, actual C.

#### N6.2 — the ratio prize ✅
**Statement.** `ratio_prize`: `∃ k₀, ∀ k ≥ k₀, I_g²/J_g ≥ (log k)/64` (with `g(u)=1/(1+Au)`, `A=log k`, `T=k^{1/8}/log k`, the N6.1 closed forms substituted).
**Role.** The variational prize: the Maynard ratio grows like log k, so it exceeds any threshold for large k.
**Proof idea.** Substitute the N6.1 closed forms; real-analysis inequality (k₀=2 sufficed).
**Lean.** `Salt.Maynard.ratio_prize` (Salt/Maynard/Ratio.lean). **Status.** ✅ 2026-07-07 (Opus, driver checked the bound genuinely grows in k). **Difficulty.** predicted C, actual C.

#### N4.4 — cross-collision correction ✅
**Statement (frozen).** The (dᵢ,eⱼ)>1 collision correction to S₁-main, bounded via the y-side by `(ck²/D₀)·A₁^k` relative.
**Role.** Makes the S₁ upper bound (N4.3) rigorous (collision pairs count 0 but the algebraic form sums over them).
**Proof idea.** Landed: the EXACT unconditional decomposition `compat = yside − collision` (`s1_compat_eq`), `s1_full_split`, `s1_yside_nonneg`, and the one-sided drop `crossCollision_le` (conditional on `0 ≤ collision`). PORT-BLOCKERed: the quantitative `(ck²/D₀)` bound on the collision form (stated as a Prop `CrossCollisionControlled`) — the genuinely hard piece, since the collision form isn't obviously signed.
**Lean.** `Salt.Maynard.s1_compat_eq`, `s1_full_split`, `s1_yside_nonneg`, `crossCollision_le` (Salt/Maynard/CrossCollision.lean)
**Status.** ✅ 2026-07-08 (Fable design + Opus execution, attempt 3) — the quantitative core landed in full: `collision_lower_order` gives `|s1CollisionForm| ≤ (12k²/D₀)·yside` with κ explicit and R-free; `crossCollisionControlled_holds` discharges the Wave-4 Prop; `compat_le_two_yside` is the form N4.3 consumes. New file Salt/Maynard/CollisionQuant.lean (2142 lines, 36 declarations, all axiom-clean). The design rests on two structural facts: pairwise coprimality makes the per-prime collision indicator an EXACT disjoint-sum identity (so the Möbius/assignment expansion stays signed with exact `T_forced` inner evaluations — no absolute values until the outermost layer), and every collision prime yields `(p−1)⁻²` (φ-growth + erasure case analysis, Q-partition with the `Σ_Q 2^{|Q|} = 3^{|P|}` binomial), giving a convergent R-free Euler tail at D₀ = k³ unamended. **Caveat for callers**: the tensor hypotheses need the ZERO-PATCHED weight `f₀ = if n = 0 then 0 else fWt k R n` (literal `fWt` has junk `fWt 0 = 1` violating divisor-antitonicity at m = 0; the patched weight induces the identical y). **Difficulty.** predicted C, actual C+ — landed only with complete Fable-level design, like N3.3.

#### N3.3 — weighted transfers ✅
**Statement (frozen).** A₁,B₁ lower at exact constant; A₁,A₁⁽¹⁾,A₁⁽²⁾ upper at 4× the N6.1 integral term.
**Role.** Bridges the atom (N3.1) to the 1-dim weighted sums the S₂ main (N5.3/N5.5) and overshoot (N5.4) consume.
**Proof idea.** Landed: the definitions (`uVal`, `fWt`, `A1`, `B1`, `A1_1`, `A1_2`), structural facts, and the reduction-to-atom lemmas (`A1_le_phiAtom`, `B1_ge_min_mul_phiAtom`, …). PORT-BLOCKERed: the actual Abel-summation transfer giving the exact-constant lower and 4×-integral upper bounds (the packaged "crude" versions committed are vacuous placeholders, NOT the real bounds — see flags).
**Lean.** `Salt.Maynard.uVal`, `fWt`, `A1`, `B1`, `A1_1`, `A1_2`, `A1_le_phiAtom`, `B1_ge_min_mul_phiAtom`, … (Salt/Maynard/Transfer.lean)
**Status.** ✅ 2026-07-08 (Fable design + Opus execution, attempt 3) — ALL FIVE sharp bounds landed: `B1_lower_sharp`/`A1_lower_sharp` at constant exactly 1, `B1_upper_sharp`/`A1_upper_sharp` at constant exactly 4, `A1_1_upper_split` pointwise; error constants explicit and R/T-free (`errB1 = φW(log2+logW)`, `errA1 = 1+8φW·log2+4(φW+1)`). Key design moves: the universal by-parts identity `F = c₁(G−w·log)+c₂w`, closed-form antiderivatives in `s = 1+B·log t`, the R-free-only constant policy, and the A1_1 pointwise reduction (no Abel needed). New file Salt/Maynard/TransferSharp.lean (919 lines); attempt-1/2 scaffolding in Transfer.lean retained. **Difficulty.** predicted C, actual C — but only after complete Fable-level design; two delegated attempts without it produced only crude bounds.

#### N4.2 — S₁ trivial error ✅
**Statement.** `s1_trivial_error_le`: the O(1)-count-error sum factors as `2^(k+1)·(Σ|λ|)²`; `sum_abs_lam_le`: `Σ_{d∈𝒟}|lam d| ≤ R^{k+1}·Σ|y|/∏φ` (polynomial in R, hence o(N)).
**Role.** Bounds the N4.1 counting error's contribution to S₁.
**Proof idea.** `Finset.sum_mul_sum` factorization; `lam_abs_le` (N2.3) + `|𝒟| ≤ R^k` + `∏dᵢ < R`.
**Lean.** `Salt.Maynard.s1_trivial_error_le`, `sum_abs_lam_le` (Salt/Maynard/S1Error.lean). **Status.** ✅ 2026-07-07 (Opus). **Difficulty.** predicted B, actual B.

#### N6.3 — concrete k₀ ✅
**Statement.** `exists_k0_ratio_gt M`: `∃ k₀, ∀ k ≥ k₀`, the ratio prize `≥ M` (k₀ abstract, `exp(64M)`-scale).
**Role.** Picks the threshold where the ratio clears any target M.
**Proof idea.** `ratio_prize` (≥ (log k)/64) + `log k ≥ 64M ⟺ k ≥ exp(64M)`.
**Lean.** `Salt.Maynard.exists_k0_ratio_gt` (Salt/Maynard/K0.lean). **Status.** ✅ 2026-07-07 (Opus). **Difficulty.** predicted B, actual B.

#### N5.1 — S₂^(m) decomposition 🟡
**Statement (frozen).** S₂^(m) = main (∝ the s2_diagonalisation RHS, r_m=1) + error (bounded by eh_error_small).
**Role.** Connects the prime-counting side to the S₂ diagonalized form.
**Proof idea.** Landed: the algebraic decomposition `s2_decomp` (S₂ = main + error, exact), `s2Main_factor` (pulls Δπ/φ(W) out, residual = the N2.5 LHS restricted to r_m=1), `s2Error_abs_le` (triangle bound to per-modulus discrepancies), over a genuine prime object `s2PrimeCount`. PORT-BLOCKERed: actually invoking `s2_diagonalisation` for the main and `eh_error_small` for the error (the two C-level interfaces).
**Lean.** `Salt.Maynard.s2_decomp`, `s2PrimeCount`, `s2Main_factor`, `s2Error_abs_le` (Salt/Maynard/S2Decomp.lean)
**Status.** 🟡 partial 2026-07-07 (Opus) — scaffolding done, the two mathematical links open. **Difficulty.** predicted C, actual C.

#### N4.3 — the S₁ upper bound ✅ (modulo threaded CRT solvability)
**Statement.** `S1_upper`: `∃ C ≥ 0, S1 ≤ 2·((K₀−1)N/W')·yside + C·R²·(1+log R)^(4k+2)` where `S1 = Σ_{n∈window} (Σ_{d∈𝒟, dᵢ∣n+hᵢ} λ_d)²`.
**Role.** The S₁ side of the Maynard ratio; `yside` cancels against S₂ in N7.1.
**Proof idea.** Genuine square expansion → `congCountTuple` (N4.1); compat/collision split; `compat_le_two_yside` (the factor 2); trivial error via the two sharp prereqs (`lam_abs_le_sharp` × `kSieveIndex_card_le`) — genuinely `o(N)` at `R = N^{1/5}`.
**Lean.** `Salt.Maynard.S1_upper`, `S1_eq_sum_dd`, `S1_le`, `S1_trivial_error_le'`, `S1`, `weightSq`, `windowSet` (Salt/Maynard/S1Bound.lean)
**Status.** ✅ 2026-07-08 (Opus, workflow + driver audit) — modulo one threaded hypothesis `hsol` (per-compat-pair CRT solvability, true but its Lean construction deferred to a `cong_solvable` lemma). **Difficulty.** predicted C, actual C.
**Notes.** Error exponent `4k+2` (driver brief said `2k+2` — an arithmetic slip the agent correctly fixed). Uses the zero-patched `f₀` per the N4.4 caveat.

### M2/M3/M4/M5/M6/M7 — remaining nodes frozen (N2.0), not yet executed

Frozen statements in `docs/blueprints/maynard.md`. Remaining: the
**diagonalization core** (N2.2 λ-from-y, N2.4 S₁-diag, N2.5 S₂-diag, N3.3
weighted transfers — the coupled C-keystones), then the M4/M5 spine
(N2.3, N4.2–N4.4, N5.1–N5.5), M6 ratio (N6.2/N6.3), M7 assembly (N7.1–N7.4).
