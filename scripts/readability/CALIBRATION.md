# Layer-1 readability: calibration (O83 item 1)

The pair was chosen BEFORE the script was first run on either: `Salt/Brun/M2.lean`, a classical sieve
instantiation in ordinary mathlib style (the "readable" pole), and `SaltC1/Cert54/`, C1's generated
`k = 54` certificate (the control, which must score low). Regenerate the table with

    python3 scripts/readability/layer1.py Salt/Brun/M2.lean --json
    python3 scripts/readability/layer1.py SaltC1/Cert54 --json

Instrument receipts. The parser counts **493** theorems in Cert54, the number `Audit.lean`'s own header
states. On M2 it agrees with plain `grep` (18 theorems, 3 definitions, 14 docstrings, 2 `decide`). The
selftest has 24 mutation arms. Of the first fifteen, twelve fail against a zero stub (red first) and the three
invariance arms (copyright excluded, module header excluded, tactic names in prose ignored) each fail against
a mutant that breaks the property they guard. Nine more (2026-10-17, a non-author's) are properties of the
scanner itself — prose, string literals, line comments, attributes and modifiers, `example`, distinct
references, self-reference, cycles — and each was shown red against a mutant of the scanner that lacks the
property before it was added. One of them found a defect: a declaration keyword at a line start inside a
multi-line string literal was counted as a declaration. The fix blanks a literal's content; measured over the
salt tree with the scanner's own splitter, 0 declaration counts moved, and the four Cert54 cells marked † below
moved only because its string contents no longer count as formal text.

| field | `Salt/Brun/M2.lean` | `SaltC1/Cert54/` (9 files) |
|---|---:|---:|
| `files` | 1 | 9 |
| `decls` | 21 | 579 |
| `theorems` | 18 | 493 |
| `definitions` | 3 | 80 |
| `depth` | 6 | 10 |
| `fanout_max` | 6 | 131 |
| `fanout_mean` | 1.81 | 2.699 † |
| `prose_chars` | 1703 | 14179 |
| `formal_chars` | 7779 | 129239 † |
| `prose_formal` | 0.2189 | 0.1097 † |
| `defs_documented` | 1.0 | 1.0 |
| `forward_prose_refs` | 1 | 2 |
| `role_lines` | 0.6111 | 0.0203 |
| `automation` | 60 | 596 |
| `automation_per_decl` | 2.857 | 1.029 |
| `kernel_comp` | 2 | 478 |
| `numeral_density` | 0.0 | 12.117 † |
| `kernel_comp` per decl (derived) | 0.095 | 0.826 |

## Verdict per metric (the rule: a metric that cannot tell the pair apart is struck)

| metric | reading | verdict |
|---|---|---|
| depth | 6 vs 10, but Cert54's per-file maximum is also 6: the gap is population SIZE | **struck** |
| fan-out | the mean is HIGHER in M2 (1.81 vs 0.4–1.1 per Cert54 file); the max is one assembly theorem | **struck** as a discriminator |
| prose/formal | 0.219 vs 0.110 over the population (2.0×); per file it does NOT separate: Cert54's interface files run 0.44–1.7 and its row files 0.02–0.06 | **kept, population level only** |
| defs-first (a) definitions documented | 1.0 vs 1.0 | **struck** |
| defs-first (b) forward prose refs | 1 vs 2 | **struck** at this pair |
| role lines | 0.611 vs 0.020 (30×) | **kept**, the strongest |
| hidden steps, all automation per decl | 2.857 vs 1.029: INVERTED, it would rank the certificate the more readable | **struck** as a readability signal |
| hidden steps, kernel computation per decl | 0.095 vs 0.826 (8.7×) | **kept** |
| numeral density (the declared extra) | 0.0 vs 12.1 | **kept** |

Three survive: **role lines**, **kernel computation**, **numeral density**, plus prose/formal at population
level. All three are certificate DETECTORS. None of them measures whether a human proof explains itself,
and a pair of two points cannot validate one that does. The struck axes (depth, fan-out, automation) are
real readability questions this pair cannot speak to: for them, layer 2's non-author reader is the
instrument. Nothing here says the prose is true of the code.

## The pole was not special (a census over every salt directory, 2026-10-17)

Run by a non-author with the same script at salt `f868c237`, one row per directory under `Salt/` and `SaltC1/`
(27 directories, 1,393 files). Role lines read **0.71–1.00 in 24 of the 27**; the bottom three are
`SaltC1/Cert54` **0.020**, `SaltC1/MaynardK` 0.305 and `Salt/MaynardK` 0.417 (the other certificate-shaped
family), then `Salt/Twelve` 0.548. `Salt/Brun/M2.lean` (0.611) sits below the tree's median, so the separation
the table shows holds against nearly any pole, and the pole's choice did not flatter the metric. Three limits the
census adds to the verdicts above:

- **numeral density** also flags `Salt/Chen` at 8.64 (Cert54 12.1; every other directory ≤ 1.7): a sieve's
  explicit constants, not certificate data. The axis conflates the two.
- **kernel computation per declaration** is robust: Cert54 0.826; next `Salt/Keller` 0.316 on 11 theorems in two
  files; every other directory ≤ 0.054.
- **automation per declaration** is inverted tree-wide, not only at this pair: `Salt/Vk` 14.6, `Salt/ExpSum` 11.7,
  `Salt/Chen` 10.0, `Salt/SW` 8.9 against Cert54's 1.03. The strike above was right.

None of this says the prose is true of the code; the census is one tool's reading of source text.

## Layer 2 on the Lean (O82, 2026-10-17): does `Salt/ThreePrimes` read like its plan?

The plan (`docs/plans/three-primes-PLAN.md`) passed the layer-2 reader test before any Lean was written: two
fresh readers given the plan alone answered 10/10 of its pre-registered "whys" with citations, against 3.5–4
for the Cert54 control. The Lean was then written from the plan. This section is the same test aimed at the
Lean, by a non-author of `Salt/ThreePrimes`: does the finished tree, read on its own, carry the plan's reasons?

**Method.** Object: the nine files of `Salt/ThreePrimes/` at `f63df7c9` (byte-identical to the tree merged in
#355). Control: `SaltC1/Cert54/` at the same head. Two fresh readers (Opus, not forks of anyone's session), each
confined to an export of exactly those two trees: no `docs/`, no other `Salt/` module, no web. Four parts per
artifact: a skeleton of the argument; "whys" answered with a `file:line` citation (an answer from outside
knowledge with no supporting passage scores 0); the hypotheses located by theorem and binder; kills. The sixteen
object whys are the plan's own ten (P1–P10, word for word from the plan's test) plus its six "what the Lean
departs from" whys (R1–R6). Criteria, the answer key (written from the plan's answers and located in the Lean's
docstrings), the pass bar (the plan's: skeleton ≥ 7/8, P ≥ 8/10, R ≥ 5/6, hypotheses ≥ 5/6, control ≤ 4/10) and a
prediction were committed to the private record before either reader was fired; the raw outputs are kept there
verbatim beside the scores. Scoring: full answer with citation 1 · partial or marked implicit by the reader ½ ·
not in the artifact 0.

| artifact | reader | skeleton | P whys (10) | R whys (6) | hypotheses (6) | control whys (10) |
|---|---|---|---:|---:|---:|---:|
| `Salt/ThreePrimes` | 1 | 8/8 | **8.0** | **5.5** | 6/6 | 5.0 |
| `Salt/ThreePrimes` | 2 | 8/8 | **8.0** | **5.5** | 6/6 | 4.0 |
| plan, for comparison | C, D | 8/8 | 10/10 | 6/6 (R, one reader) | 6/6 | 4 · 3.5 |

**Result, said plainly.** The Lean passes every object bar, at the bar on the plan's ten whys: both readers
score 8.0, and both lose exactly the same four half-points. P1 (why Λ-weights): the Lean states the price of
the weights (`Count.lean`) and never the reason that the tools are Λ-statements. P3 (why N₀ is ineffective):
`MajorArc.lean` names Siegel–Walfisz as the source and never says why that theorem's constant cannot be
computed. P8 (why not two primes): not in the artifact. R5 (why no lower bound on φ(q) is needed): the
mechanism is there (`Assembly.lean`), the sentence is not. Everything else the plan explains, the Lean
explains, with the readers citing the same passages the key named. **The control did not stay under its bar
for one reader** (5.0 and 4.0 against ≤ 4), so the pre-registered separation condition failed: on a Lean/Lean
pair this method separates by 8 vs 4–5, not the 10 vs 3.5–4 it showed on a prose/Lean pair, because a reader
given a certificate whose closed forms carry its normalisations reconstructs some "whys" from the formulas.
The prediction committed in advance named the same four weak spots and their modules; it was wrong on the
headline direction by one half-point (it predicted 7.5, a fail; P5, why P is a power of log N, scored 1 for
both readers from `MajorArc.lean`'s stated Siegel–Walfisz range).

**Kills, all confirmed at the object, none a false theorem statement.** Seven docstrings disagree with the
code beneath them: `MinorArc.lean:33` says K ≤ 3 log N where the code uses K ≤ 4 log N; `MinorArc.lean:34` says
the q > N case uses ψ(N) ≤ 2N where the code uses N log N; `MinorArc.lean:25` states a Step-7 inequality that is
not the one `Assembly.lean` consumes; `Count.lean:24–25` accounts for the third logarithm differently from the
proof, which pads (log N)² to (log N)³; the docstring at `Assembly.lean:232–233` promises three facts and the
statement gives one; `Arcs.lean:18` says N ≥ 2P² where the theorem needs 2P² < N; `MajorArc.lean:44–45` says
A + 2B + 1 where the code asks A + 2B. Fixing them, with the four missing sentences above, is a docs-only change
owed by the Lean's author. Both readers' closing paragraphs add what no pre-registered why asked: the
minor-arc estimate's content is an imported black box the nine files only parametrise, so a reader learns how
the pieces fit and not the hard analytic estimate.

**Limits.** The ten whys were written for the plan, and the plan was revised against them, so a pass shows the
Lean answers the plan's questions, not the questions a reader would ask of Lean unprompted. Two readers of one
model. The control bar was set for a prose/Lean pair. The scoring rule rewards a reader's candour: the same
control content scored ½ in the plan's round when the reader added "the reason is never stated", and 1 here when
the reader did not; a future round should score the artifact (does it state the reason?) and record the
reader's self-mark separately. Nothing here is a verification claim about any theorem; the kernel's verdict on
`three_primes` is its CI build, and this section measures only whether the prose explains it.

### Round 2 (2026-10-17, after the author's docs-only fix #363): score the artifact, not the reader

**Why a second round.** Round 1 left two questions. The control exceeded its bar for one reader under a rule that read a
cell at ½ when the reader *marked* it partial, so the same control content scored 1 for a reader who did not add "the
reason is never stated" and ½ for one who did: the rule paid the less candid reader. And the four missing sentences it
named were then written (#363, docs only). Round 2 fixed a **by-the-artifact rule** in the private record before any of
#363's text was read (committed 51 s after its merge; the rule's substance is in round 1's record from before #363 was
opened), re-scored round 1's raw outputs under it, and ran two fresh readers on `Salt/ThreePrimes` at `72fc6043` with
`SaltC1/Cert54` (byte-identical to round 1's) as the control, same protocol, same sixteen whys, same key.

**The rule.** A why scores 1 if the passage the reader cites *states the reason*; ½ if the cited passages state the
mechanism or the components and the reader derived the rest; 0 if the answer is not in the artifact or comes from outside
knowledge. The reader's own mark ("stated", "partly", "not in artifact") is recorded in a separate column and never scores.

| artifact | reader | skeleton | P whys (10) | R whys (6) | hypotheses (6) | control whys (10) |
|---|---|---|---:|---:|---:|---:|
| round 1 re-scored, `f63df7c9` | 1 | 8/8 | 7.5 | 5.5 | 6/6 | 4.0 |
| round 1 re-scored, `f63df7c9` | 2 | 8/8 | 7.5 | 5.0 | 6/6 | 3.5 |
| round 2, `72fc6043` | 1 | 8/8 | **10.0** | **6.0** | 6/6 | 3.5 |
| round 2, `72fc6043` | 2 | 8/8 | **10.0** | **6.0** | 6/6 | 3.5 |

**Result, said plainly.** Under the artifact rule the control stays at or under its bar in all four readings, so the method
**separates a Lean object from a Lean certificate**: by 10 against 3.5 at `72fc6043`, by 7.5 against 3.5–4 at `f63df7c9`.
Round 1's object, re-scored, reads 7.5 — *below* the bar it had passed: the artifact at `f63df7c9` stated Siegel–Walfisz's
range and P's definition and never that the one is why the other is a power of log N (P5), and the self-mark rule had
credited the readers' correct derivation to the text. At `72fc6043` **the four gaps are closed**: `Count.lean:18–21` says why
Λ; `MajorArc.lean:24–27` says why Siegel–Walfisz's constant cannot be computed; `Assembly.lean:27–30` says why three primes
and not two; `Assembly.lean:42–43` says why no lower bound on φ(q) is needed. Each is written as a reason, and both readers
cited each without prompting. None of round 1's seven docstring kills was raised again.

**Kills, confirmed at `72fc6043`, none a false theorem statement.** `Arcs.lean:25` says "1 ≤ a ≤ q because α lies in the
window", but the proof derives a ≤ q only in the branch q ≤ P, using 1/P ≤ 1/q and 2P² < N; one reader's counterexample
(N = 1000, P = 1, α = 1.001) stands. `Assembly.lean:42–43`, the new sentence, overstates: the Euler-product bound spends
1/(p−1)² ≤ 4/p², a lower bound on φ at primes, so "no lower bound of the shape φ(q) ≫ q^{1−ε}" is what is true. A
repaired sentence is a fresh claim. `SingularSeries.lean:39–40` says the product "converges, so it is at least a constant
c₀ > 0 that does not depend on N"; convergence for each N gives no uniform bound, and the proof uses log(factor) ≥ −8/p².
`Arcs.lean:59–60` calls 2P/N "the arcs' total width"; it is one arc's. Docs-only fixes, the author's.

**What the round says about the method.** Both readers marked six cells "partly" where the artifact states the key's
reason — each time the missing half is a counterfactual the key did not ask for ("o(N) would not do", "a power of N is
impossible", "a rate would need φ(q) ≫ q^{1−ε}") or a sub-why it did not pose. Under round 1's self-mark rule the same
outputs would read 9.0 on the plan's whys and 4.5 on the Lean's, failing the second bar on text that states every reason.
Round 1's self-marks had leaned the other way, three times on the control. A rule that scores the reader's mark is
unstable in both directions on the same kind of text; the artifact rule is the one to keep.

**Limits.** The scorer wrote the rule and re-scored round 1; every cell is published in the private record with the passage
it reads, so a non-author can re-read it, and the six "partly" cells are where to start. The four new sentences were
written by the Lean's author knowing round 1 had named them: a pass there shows the sentences landed and read as reasons,
not that an unprompted reader would have asked. Two readers of one model; object and control share a language; the readers'
reports reached the record as returned text, not as files they wrote. Nothing here is a verification claim about any
theorem; the kernel's verdict on `three_primes` is its CI build.
