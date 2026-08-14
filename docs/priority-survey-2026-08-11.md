> Provenance: copied 2026-08-14 from the private campaign register into salt for public citation.
> The document below is preserved whole and unedited; its original stamp (state as of 2026-08-11) stands.
> Cited by papers/flagship/main.tex; the survey re-runs before submission per its own cadence ruling.

# PRIORITY AUDIT — MERGED VERDICT (5 lanes, 12 claims, state as of 2026-08-11)

## THE TABLE

| # | Claim | FINAL | Strongest evidence (from any lane) | URL |
|---|---|---|---|---|
| 1 | Siegel–Walfisz | **STANDS** | Hostile-witness confession, dated after salt's landing: the only Lean BV project declares `axiom siegel_walfisz (A C : ℕ) {x} (hx : 2 ≤ x) {q} … : \|chebyPsi x a - x/φ q\| ≤ C_SW A C * (x/(log x)^A)` in `BV/Axioms.lean`, and its README says SW "would be a larger project… I would be very happy to get involved." Author = Arend Mellendijk, who wrote mathlib's `SelbergSieve`. Corroborated by lean-lang.org's eval board listing SW under "Mathlib lacks". | github.com/FLDutchmann/lean-bombieri-vinogradov/blob/master/BV/Axioms.lean |
| 2 | Unconditional BV-grade level of distribution → bounded gaps | **STANDS** (most perishable row) | `theorem bombieri_vinogradov … := by sorry` + `def C_BV (A : ℕ) : ℝ := sorry` in `BV/MainResults.lean`; 37 sorries tree-wide; PNT+'s entire BV chapter is a one-sentence pointer to that repo. AxiomMath does **not** have BV either — `def BombieriVinogradov : Prop := ∀ θ < 1/2, Nat.HasLevelOfDistribution Set.univ θ 1` is a *hypothesis* in their Challenge.lean. | github.com/FLDutchmann/lean-bombieri-vinogradov/blob/master/BV/MainResults.lean |
| 3 | Chen I + Chen–Goldbach | **STANDS** | Third-party dated register, not our own absence-search: lean-lang.org eval `chen_theorem` = "Not yet solved," notes name the missing input as a Brun-style weighted/lower-bound sieve. 1000-plus tracker Q1317350 carries no formalization block in any system. Only "Chen" in PNT+ is `namespace ChengGraham2004` (author collision). | lean-lang.org/eval/problems/chen_theorem/ |
| 4 | Rosser–Iwaniec linear sieve, both sides, chain form | **STANDS — with a mandatory fence** | mathlib **does** have `Mathlib/NumberTheory/SelbergSieve.lean` (405 lines). Read, not greped: every headline is one-directional (`≤`), Λ² upper-bound only, no fundamental lemma, no lower side, no chain. Three lanes independently confirm. Never claim "first sieve theory in a proof assistant" — that is false and one click from refutation. | github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/SelbergSieve.lean |
| 5 | VK 3/4-power ZFR + Littlewood-strength ZFR | **THREATENED** | Narrow claim survives: `Korobov language:lean` = 0 GitHub-wide; every competing region read at source is classical de la Vallée Poussin — StrongPNT `PNT4_ZeroFreeRegion.lean` gives `1 - A/log(\|t\|+2)`, AFP `PNT_with_Remainder` gives `1 - 1/(952320·log(\|γ\|+2))`, PNT+ merged the same shape as PR #1635 on 2026-08-04. But the *neighbourhood is occupied since Sept 2025*, so any shortening to "first machine-checked zero-free region" is FALSE by 26 months. | github.com/math-inc/strongpnt |
| 6 | Vinogradov Mean Value Theorem | **STANDS** | Zero VMVT/efficient-congruencing/decoupling artifact in any system. Two near-misses opened and cleared: AFP "Wooley's Discrete Inequality" is the elementary `min_r (r + λ/r) ≤ √(4λ+1)`; the only Lean files named `VinogradovMeanValue.lean` are HautevilleHouse decoys (`structure X where field : Prop` + a theorem projecting its own hypothesis). "Ford 2002 formalized in PNT+" was a WebFetch artifact — no Ford file in the 70-file IEANTN tree. | isa-afp.org/topics/mathematics/number-theory/ |
| 7 | Large sieve (analytic/arithmetic/character) + BDH | **THREATENED** | The inequality itself is unproved everywhere — axiomatized verbatim in `BV/Axioms.lean` (`axiom large_sieve … ≤ C_LS * (N+Q^2) * ∑ ‖c n‖²`), and gersh/ternary-goldbach-lean's 30-file LargeSieve tree carries 7 sorries per file and leaves the sharp constant as an open predicate. **But the analytic engine fell 1 day ago**: anthropics/zeta-23-lean proves `theorem mvDiag_thirteen : MVDiag 13` sorry-free (Montgomery–Vaughan generalised Hilbert inequality). Mellendijk's README calls the large sieve "simple enough to be its own single-person project." Cheapest claim on the list for someone else to erase. | github.com/anthropics/zeta-23-lean |
| 8 | Vaughan's identity | **FALLEN** | Two independent public counterexamples, both proved, both sorry-free, both predating salt's 2026-07-11. (a) `BV/Defs.lean:368 theorem Lambda_decomp (n : ℕ) : Λ n = Λ♯ n + Λ♭ n + Λ≤U n`, dated by pickaxe over 21 commits: sorry present through dd62871 (2026-03-18), **gone from 3ed4968 (2026-03-20)** — four months early. (b) `MinorArcVaughan.lean:180 theorem vaughan_identity_finite (U V n) : Λ n = vaughanLambdaLow V n + vaughanTypeIArithmetic U V n + vaughanTypeIIArithmetic U V n`, four-step calc, 7508-line file, zero sorries, internal docs dated 2026-06-18. | github.com/FLDutchmann/lean-bombieri-vinogradov/blob/master/BV/Defs.lean |
| 9 | Kloosterman ‖S(a,b;p)‖ ≤ 2√p via Stepanov | **THREATENED** | Narrow claim clean: `Kloosterman` = 0 hits in mathlib, PNT+, ternary-goldbach, AFP; the only 17 Lean hits are the HautevilleHouse decoy family, whose `weil_bound_classical … := by sorry` was read. **But the method claim is public since Feb 2026**: math-inc/RiemannHypothesisCurves is sorry-free Bombieri–Stepanov for hyperelliptic curves following Iwaniec–Kowalski **ch. 11** — same chapter, same method as salt's Weil/Descent — terminating in `\|(q:ℝ) - N\| < 5 * f.natDegree * √q` and `#print axioms riemann_hypothesis_hec`. | github.com/math-inc/RiemannHypothesisCurves |
| 10 | Maynard–Tao k-dim sieve load-bearing + explicit gaps ≤ 12 under EH | **FALLEN as bundled** (≤12/EH residue stands) | AxiomMath/PrimeGapsLib, public 2026-08-08, **pushed 2026-08-11 during the survey**. Audited by two lanes independently, not trusted from README: 431 .lean files, 91,856 lines, zero sorries outside the deliberate comparator stub, zero axiom decls, zero `native_decide`, zero `opaque`. Load-bearing Maynard apparatus: `MaynardSieveDatum`, `MaynardWeight`, `MaynardG`, `GPYSieveS1`, `EnlargedSimplex`, `Tuple/H50.lean` (Polymath8b 50-tuple, diameter 246), `Gap600/Witness.lean` (M₁₀₅ > 4 in cleared-denominator integers). Ships a leanprover/comparator harness. **Survives:** nobody is below 246; theirs is BV-conditional, salt's ≤12 is EH-strength. **Dies:** "first Maynard–Tao k-dimensional sieve in load-bearing form." | github.com/AxiomMath/PrimeGapsLib/blob/main/PrimeGaps/Bounded246.lean |
| 11 | Parity wall / twin-bar as kernel objects | **STANDS on priority — do not use the word "first"** | Uncontested everywhere, and one lane found *positive dated corroboration*: gotrevor/bounded_gaps `Polymath8b.lean:707-718` records that it **deleted its own** `parity_barrier` axiom because "the wrapper was opaque with no destructor… pure documentation-as-axiom, never consumed," then writes down as future work the exact reformulation salt performed (non-existence over a named class of Selberg-type square weights with a precise threshold), adding "Polymath8b doesn't do this either; the §7 statement is informal." | github.com/gotrevor/bounded_gaps/blob/master/BoundedGaps/Polymath8b.lean |
| 12 | MRT/Halász machinery; log-Chowla-2 reduced to one named door | **STANDS** | No MR/Halász/Chowla content in mathlib, PNT+, AFP, or Rocq. `Halasz language:lean` = 0; all 8 `Chowla` Lean hits disqualify (Bruck–Ryser–Chowla in finite geometry, plus crank repos, one of which opens `axiom R : Type` "to avoid analysis complexity"). Tao's IEANTN personal log through Day ~139 is explicit-constant PNT throughout — no multiplicative-function machinery, no large sieve, no SW, no Kloosterman. | github.com/AlexKontorovich/PrimeNumberTheoremAnd/wiki/Terence-Tao's-personal-log |

## CONFLICTS BETWEEN LANES — AND THE PATTERN IN THEM

Lanes disagreed on **6 of 12**: claims 5 (4–1), 7 (3–2), 8 (3–2), 9 (4–1), 10 (3–1–1), 11 (3–2).

**In five of those six, the minority verdict is the one grounded in a file that was opened, and the majority STANDS rested on search-hit absence.** Claim 8: three lanes greped `Vaughan`, cleared two author-name collisions (`MyMV_A3a.lean` in a directory named `Unused`; `PVIdentity.lean` = Cauchy principal value), and declared it clean — but FLDutchmann calls the theorem `Lambda_decomp` with `Λ♯/Λ♭` notation, so a name-grep cannot see it. Claim 10: three lanes checked gotrevor/kewowski scaffolds and never saw a repo that was 3 days old. Claim 9: one lane affirmatively searched "Stepanov method / RH for curves in Lean" and reported *zero results* against another lane's clone-and-read of a sorry-free Stepanov development — a direct contradiction, resolved in favour of the read. **Absence-by-grep lost every time it was tested.**

Claim 11 is the exception: the two dissenting lanes returned NO-SIGNAL, i.e. declined to certify a *first* for a reference class nobody else has posed. That is a presentation objection, not a priority finding, and I have not rounded it into STANDS — the table records it as STANDS on priority with the word "first" struck.

**Two bookkeeping conflicts to fix in the docs.** (a) `FLDutchmann/lean-bombieri-vinogradov` and `amellendijk/lean-bombieri-vinogradov` are the same repo under two handles; pin one before citing or a checker gets a 404. (b) The brief's "Song–Yao 2025" is wrong: the AFP artifact `PNT_with_Remainder` is dated **2024-05-05** (2025 is the JAR paper). Carrying the artifact date matters — it sits *before* several salt landings.

## THE CROSS-CUTTING DEFECT (not a row — the whole file)

**Every surviving "first" is a first on a private tree.** Salt's dates precede both real counterexamples (Maynard capstone 2026-07-09 vs PrimeGapsLib 2026-08-08; MV-Hilbert 2026-07-19 vs zeta-23-lean 2026-08-10), but a private repository cannot establish priority against a public artifact. The honest form of every row is "first public" or "first, on a private tree dated X" — never the bare "first". This is one documentation defect, not twelve, and it is the same shape as the M1(d) lapse: the measurement is correct, the characterization is too broad.

Separately, **the meta-claim of scale is now the weakest sentence in the package**, weaker than any of the twelve: EconCSLib (arXiv 2606.13306, Nikhil Garg, single researcher, LLM-generated, public 2026-07-02) is **986,391 lines** of Lean 4 in an overlapping window — larger than 658k, solo, AI-driven, already public. Restate as domain-specific ("largest formal *analytic number theory* corpus") and never as a raw line count.

## THE HEADLINE SENTENCE THE NATURE TRACK MAY HONESTLY USE

> As of 2026-08-11, no public artifact in any proof assistant proves the Siegel–Walfisz theorem, the large sieve inequality, Bombieri–Vinogradov, a lower-bound (linear/Rosser–Iwaniec) sieve, Chen's theorem, the Vinogradov mean value theorem, the Weil bound for Kloosterman sums, a zero-free region beyond de la Vallée Poussin strength, or any Matomäki–Radziwiłł/Halász machinery — the two live external analytic-number-theory formalizations take Siegel–Walfisz and the large sieve as *axioms* and say so in their own source — and salt's tree carries machine-checked proofs of all of them, dated 2026-07 on a repository that was private until this publication.

That sentence is defensible line by line, cites adversaries rather than asserting absence, and uses no unqualified "first". **Do not strengthen it in any of these four ways**: not "first zero-free region" (false since Sept 2025), not "first sieve theory" (false — mathlib has SelbergSieve), not "first Vaughan's identity" (false since 2026-03-20), not "first Maynard–Tao sieve" (false since 2026-08-08). Vaughan and the Maynard sieve must be *removed from the firsts list entirely* and restated as independent formalizations.

## THE THREE VERDICTS THAT MOST NEED A HUMAN BEFORE PUBLICATION

1. **Claim 8 (Vaughan — FALLEN).** Three of five lanes said STANDS and all three were wrong for the same mechanical reason. A human must open `BV/Defs.lean:368` and `MinorArcVaughan.lean:180`, confirm each is the same theorem as `Salt.LS.vaughan` (the defensible-looking distinction — explicit nested-finite-sum form vs arithmetic-function convolution form — is a *packaging* difference, not a priority defence), and strike the row. A published false "first" is the single worst outcome available here.
2. **Claim 10 (Maynard–Tao — FALLEN as bundled).** A real, funded, verified competitor appeared during the survey and pushed again mid-audit. The human decision is not factual but editorial: whether private internal dates are asserted as priority at all, and confirmation that the ≤12/EH residue is genuinely uncontested (both lanes that audited PrimeGapsLib say nobody is below 246, and their input is BV-conditional).
3. **Claim 9 (Kloosterman — THREATENED).** The only lane-vs-lane factual contradiction in the audit: one lane searched for Stepanov-in-Lean and found nothing; another cloned math-inc/RiemannHypothesisCurves and read a sorry-free Bombieri–Stepanov proof following the *same IK chapter*. Single-source, contradicted, and it decides whether "first Weil-grade square-root cancellation via Stepanov" may appear in any form.

**Runners-up, both single-lane finds that no other lane saw and that should be re-opened by hand:** claim 7's `mvDiag_thirteen` in anthropics/zeta-23-lean (decides whether MV-Hilbert can be claimed at all — salt's is 3 weeks earlier but private), and claim 5's exponent convention (salt says "3/4-power"; standard VK normalization is 2/3 in `1 - c/((log t)^{2/3}(log log t)^{1/3})` — a referee will read an undefined convention as an error). Two GitHub code searches are also **owed, not dropped**: camelCase `ZeroFreeRegion`, and the phrase search for Vinogradov mean value, both cut off by rate-limiting.

**Re-survey cadence:** weeks, not months. The decisive artifacts are dated 2026-03-20, 2026-08-07, 2026-08-08, 2026-08-10, and 2026-08-11. Watch AxiomMath (moving weekly), lean-bombieri-vinogradov (the day its two axioms discharge, claims 1/2/7 all move at once), and PNT+/IEANTN (the only plausible home for a VK-grade bound reaching 5/6).
---
# ADDENDUM (maestro, 8/11 ~11:15, at-source closures of the three human checks)

**1. VAUGHAN — FALLEN, CLOSED BY THREE HANDS.** The audit quoted it; math ruled SAME THEOREM
from the banked quotes (11:12, filename collision with our own MinorArcVaughan.lean excluded,
its no-network limit declared); the maestro fetched the external bytes:
`theorem Lambda_decomp (n : ℕ) : Λ n = Λ♯ n + Λ♭ n + Λ≤U n`, sorry-free, with the
Λ♯/Λ♭/Λ≤U Vaughan-decomposition defs beside it (raw.githubusercontent, FLDutchmann master).
Strike from every firsts list, everywhere, permanently.

**2. KLOOSTERMAN — BOUNDARY DRAWN AT THE SOURCE.** math-inc/RiemannHypothesisCurves is REAL:
Bombieri–Stepanov for hyperelliptic curves (|N−q| ≤ 5m√q, IK ch.11), ~4,000 ln, and
**AI-generated by "Gauss, Math Inc's frontier autoformalization agent"** with human-guided
LaTeX blueprint. It contains NO Kloosterman sums. ⇒ the METHOD claim ("first Weil-grade
square-root cancellation via Stepanov") is DEAD; the KLOOSTERMAN-SPECIFIC claim (Weil 2√p
through the Estermann composite assembly, public-artifact-first as of the survey) SURVIVES.
Claims must be object-specific, never method-general.

**3. ZETA-23-LEAN — FAR LARGER THAN THE AUDIT'S ROW, AND IT RESHAPES THE LANDSCAPE SECTION.**
anthropics/zeta-23-lean is a COMPLETE sorry-free artifact: >2/3 of zeta zeros on the critical
line (Theorems A–E incl. simple-zeros 2/3, distinct-zeros 5/6, Dirichlet L analogues), axioms
= the standard three, Lean v4.33.0-rc2, comparator-directory trust pattern, ported PNT+ code
attributed. **Authored by Claude; the companion paper is credited "Claude; Anthropic, San
Francisco, 2026."** Carries publicly: the MV generalized Hilbert inequality (claim 7's engine
— salt's 7/19 private landing predates by ~3 weeks but cannot claim priority), Weil's explicit
formula, Riemann–von Mangoldt.

**LANDSCAPE CONSEQUENCE (for the Nature draft §4/§9 and the inquiry):** the AI-formalization
field has ARRIVED, not emerged — at least four industrial-grade public artifacts in our exact
space within weeks (AlphaProof/DeepMind · Gauss/math-inc · zeta-23/Anthropic-Claude-as-author
· AxiomMath/PrimeGapsLib · plus EconCSLib solo at 986k ln). The case study's differentiation
is therefore EXACTLY: (a) the one-human + consumer-subscription fleet configuration vs lab
systems; (b) the full vertical to fabricated silicon; (c) the documented epistemics (the error
ledger, the laws, the retraction discipline); (d) the measured economics. "AI-scale
formalization" as a genre belongs to no one and the paper must cite all of the above. The
re-survey cadence ruling (weeks) is CONFIRMED from inside a single day.

---
# ADDENDUM 2 (maestro, 8/11 ~17:2x — the zeta-23 ANNOUNCEMENT, found by the Captain's wife)
**anthropic.com/research/riemann-zeta, published AUGUST 10, 2026 — one day before this
audit.** The post upgrades the repo's characterization: not a formalization of known
mathematics but A NEW RESULT — the lower bound for zeta zeros on the critical line
satisfying RH raised 41.6% → 67.2%, "an unintended byproduct" of Claude attempting RH
itself. Facts the repo didn't carry: Claude autonomous across two Claude Code sessions,
31M output tokens, ~60 subagents, ~1.5 days; the human's input "mostly limited to
messages of encouragement"; Anthropic mathematicians validated; EXTERNAL review by Conrey
and Goldston; Lean formalization "passes the standard validation tool comparator."

## CONSEQUENCES FOR THE PAPER
1. §1's landscape clause upgrades (new-result, not formalization) with the announcement
   cited — the field's question has publicly moved to exactly what our paper answers.
2. THE DIFFERENTIATION SHARPENS: their configuration = inside the lab, unreleased research
   model, staff validators. Ours = one person, consumer subscriptions, outside any lab,
   full stack to tapeout, complete accounting. Complementary papers: capability ceiling
   (theirs) vs accessibility + method + the vertical (ours) — published within days.
3. A PUBLIC COMPARABLE for token-scale exists (31M tokens / ~1.5 days / one result vs our
   metered 28.07M / 4.86 days inside a 36-day program) — a landscape datum, NEVER a ratio.
4. The "window is closing" urgency of the original block is now validated from the top of
   the field, the day before our approval filing.
