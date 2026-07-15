# salt — writeup pre-outline

One document, per JYH 2026-07-14: artifacts, audiences and tone, results to
present, paper sketches, and the "clone-and-continue" repo vision. This is
the planning root; each artifact gets its own skeleton when drafting starts
(after the Chen headline lands and the merge is done).

---

## 0. The claim (one sentence per audience)

- **To mathematicians:** we formalized a large body of classical analytic
  number theory — culminating in an unconditional Chen's theorem — and the
  process produced a complete, kernel-checked ledger of every correction the
  classical presentation needed: ~69 catches, none in the celebrated ideas,
  all in the connective tissue.
- **To the ITP / AI-for-math community:** a machine-checked corpus that
  would classically be estimated at many person-years of formalization
  effort was built in days of wall-clock under an AI-orchestrated method,
  with the human in a ratification role.

## 1. Artifacts

**A. The anatomy paper** (mathematician-facing).
"The X-ray of a classical proof": what formalizing Chen's theorem revealed
about where correctness actually lives. Built on the catch ledger.

**B. The method paper** (ITP / systems venue).
The Salt method: the model cascade (design/gate/verify/commit vs execute),
adversarial gates before freezes, STEP-0 inventories, the ceremony
discipline, catch-driven iteration, model routing and token economics.
This is where the "time of automated proving has arrived" thesis lives,
with receipts.

**C. The living artifact: the repo itself.**
Not a tarball attached to a paper — a continuable research environment.
Target experience: *clone the repo, run `claude`, and the session knows the
project* (CLAUDE.md routes any model tier to appropriate work; the
blueprints define open nodes; flags.md carries the institutional memory).
See §5 for the gap list.

**D. (optional) The catch ledger as a dataset.**
Machine-readable version of flags.md: 69 entries × (wrong claim, how
caught, diagnosis, repair, category). Nothing like it exists at this scale;
useful to proof-engineering and AI-evaluation communities independently of
the papers.

## 1½. The mathematician claim, stress-tested (devil's-advocate session, 2026-07-14)

The attack (JYH as devil's advocate): formalizing known work is service, catches
were expected (every big formalization found gaps; the community's prior is
"proofs have local gaps, theorems are fine" and 69-catches-zero-false-theorems
*confirms* it), the bounds aren't records, and there is no new theorem.

**Conceded, and the paper says so on page one:** no new theorem; "we found
catches" is not news and must not be the thesis; drop "better bounds" from the
pitch entirely unless a drafting-time audit against the explicit-ANT literature
(explicit zero-free regions, Akbary–Hambrook-style explicit BV) shows a genuine
record — our constants are explicit-but-worse (tower thresholds).

**What survives — the four claims the paper actually makes:**

1. **The mechanism, not the distribution.** The serious catches (#64, #65,
   #69) were statement packages individually true and individually checkable
   but JOINTLY uninhabitable — a failure mode reading cannot detect even in
   principle. And our own carefully-written designs produced it at the same
   rate as the literature until adversarial satisfiability-gating was added.
   So "the community would have caught these" is wrong in an interesting way:
   the process that catches them is instantiation, not refereeing, and nobody
   was running it. Epistemology with data, not a gotcha.

2. **The terrain was chosen adversarially.** Analytic NT (uniformities,
   log-power bookkeeping, "by dyadic decomposition we may assume") is the
   consensus worst case for formalization — which is why 40 years of proof
   assistants produced essentially none of it. The demonstration is: the
   hardest genre of informal mathematics is no longer out of reach, at
   person-days of attention. The reader's correct update is about their own
   Monday morning: kernel-checking THEIR load-bearing lemma is now cheap.
   The clone-and-continue repo is this argument made concrete.

3. **The refutation engine (the strongest claim).** What kills attacks on
   hard problems is not lack of ideas but late discovery that lemma-packages
   are jointly incompatible — found by hand, months in, sometimes post-
   publication. We demonstrated the cheap version four times in one day:
   adversarial instantiation returns either a kernel-checked "uninhabitable,
   here is the witness" or a green light, BEFORE proof effort is spent. For
   the frontier this is a design instrument, not a verification service. The
   M₂ ≤ 2 log 2 no-go is the same instrument pointed at a method: parity-
   barrier folklore turned into a theorem with an exact formal boundary —
   and the boundary IS the research program.

4. **The proof became an object.** Chen has been cited for 50 years as a
   monolith; nobody builds on the interior because the interior is prose.
   Ours is queryable and re-runnable (which hypotheses are load-bearing for
   the constant; what changes at a different distribution level) — a new
   kind of access to old mathematics, and the honest sense in which
   something mathematical was produced.

**Page-one framing sentence:** *we didn't add a theorem to number theory; we
changed what it costs to know one, to build on one, and to kill a wrong path
to one.* Rejecting all four claims amounts to claiming mathematicians don't
care about certainty, reuse, or failed attempts — and the history of this
exact problem (Chen's interior unaudited for fifty years, the parity barrier
as folklore, a century of dead twin-prime attacks) says otherwise.

## 2. Audiences and tone

| Audience | Tone | Leads with | Never says |
|---|---|---|---|
| Mathematicians | measured, modest, evidence-first | the ledger and its distribution | "referees are obsolete"; any unanchored speed claim |
| ITP / AI-for-math | direct, quantitative | scale + cost + method | hand-waving about rigor (this crowd checks) |

Calibration rules for both: state up front that no new theorems were proven
(the frontier claim is about *method*, not results); anchor every speed
claim to cost-of-attention (person-days of human decision points, tokens,
wall-clock); the honest comparisons are Flyspeck (~20 person-years) and the
Liquid Tensor Experiment (~1+ community-year for one theorem).

## 3. Results to present (inventory — verify each against the repo at drafting time)

Headline theorems (kernel-checked, axioms ⊆ [propext, Classical.choice, Quot.sound]):
- Brun's theorem track (branch `brun`).
- Twin almost-primes: Ω(n(n+2)) ≤ 20 infinitely often (P0/P1 rung).
- Unconditional Siegel–Walfisz (`siegelWalfisz_holds`) — the full classical
  zero-theory arc: 3-4-1 positivity, quantitative zero-free region, the
  zeta/χ₀ pole bound, Siegel's theorem machinery, contour work.
- Bombieri–Vinogradov chain (`bounded_gaps_of_siegelWalfisz`) and
  unconditional bounded prime gaps (`bounded_gaps_UNCONDITIONAL`);
  the explicit12 track (gaps ≤ 12).
- Large-sieve infrastructure: analytic + arithmetic LS, character LS,
  Gauss sums, Vaughan, BDH, dispersion.
- **Chen's theorem (pending — the PRICE wave):**
  `{p | p.Prime ∧ IsP2 2 (p+2)}.Infinite`, unconditional.

Numeric certificates worth exhibiting: the kernel-certified razor margin
(M = 0.012151 ≥ 1/100), the 600-panel c̄ certificate, the mass-ledger
super-solution (Neumann domination), the D0-window witness, the tower
operating point.

The ledger: 69 catches, 0 proofs on wrong statements. Taxonomy (to be done
as the first drafting task — it only reads flags.md):
1. transcription/rendering gaps (classical prose → precise statement),
2. estimate-vs-statement divergences (the proof needs less than the
   statement demands, or the statement demands the impossible: #64, #66,
   #69),
3. genuinely elided arguments (the "obvious" steps: the dyadic pricing
   layer, the W-trick seam #65, the diagonal aggregation #68).

Method stats to compile: nodes landed / first-attempt rate (e.g. the seven
consecutive first-attempt FULLs after the H2 gate), catches by discovery
mechanism (gate / STEP-0 / executor / kernel), pre-construction catch rate
on terminal nodes (4 of 4 at the end), tokens and wall-clock per arc.

## 4. Paper sketches

**A. Anatomy paper** — sections:
1. Chen's theorem and why it resisted formalization (history: 1966/1973,
   the switch, the bilinear estimate).
2. What we built (the corpus, one page; pointer to the repo).
3. The ledger and its distribution (the central section: ideas held,
   interfaces didn't; the taxonomy with exhibits).
4. Three case studies: the one-sentence dyadic decomposition that became
   five catches and a pricing layer; the uninhabitable H-package (#65 —
   shape-correctness vs satisfiability); the estimate-vs-statement genre
   (#64/#69 — true estimates wearing false statements).
5. The no-go theorem: M₂ ≤ 2 log 2 kernel-checked — the k = 2 instance of
   Polymath8b's M_k ≤ (k/(k−1))·log k, but formalized: the parity barrier
   as a theorem about a precisely-delimited method class, and (pending a
   literature sweep) the first machine-checked limitative theorem about a
   named proof method. The formal class boundary is the research object.
6. What this changes — the four §1½ claims: the mechanism (instantiation
   catches what reading cannot), the worst-case terrain demonstration,
   the refutation engine as frontier instrument, the proof as queryable
   object. Verification economics and explicit constants as supporting
   material, not the thesis.

**B. Method paper** — sections:
1. The result as benchmark (what was proven, at what cost).
2. The Salt method: roles (design/gate/execute/verify), Iron Rules,
   blueprints, difficulty classes, the flags ledger as institutional
   memory.
3. Adversarial gating and STEP-0: why satisfiability checking of statement
   packages is the load-bearing discipline (evidence: the terminal-node
   catch sequence).
4. Orchestration mechanics: model routing (and the Fable-inheritance
   budget lesson), resume-on-failure, ceremonies with explicit exit codes,
   parallel waves with file-disjoint executors.
5. Economics: tokens per node, per arc; what Opus vs Fable tiers
   contribute; comparison to human formalization efforts.
6. Limits and failure modes observed (honest section: the API-instability
   tax, the catch that took three terminal attempts to surface, what the
   method still can't do).

## 5. The clone-and-continue artifact — gap list

Already in place: CLAUDE.md session protocol with tier routing;
docs/MODEL_POLICY.md; blueprints with pre-classified nodes; flags.md;
Apache-2.0 headers; lake/elan pinning; mathlib cache via `lake exe cache get`.

To add before announcing:
1. **README quickstart**: clone → `elan` install → `lake exe cache get` →
   `lake build` (expect green) → `claude` → "read CLAUDE.md and the current
   blueprint; pick a node at your tier."
2. **ONBOARDING.md**: the method in one page for a newcomer (human or
   agent); how to read a blueprint card; what a ceremony is; how to flag.
3. **METHODS.md**: per the ratified Night Cycle plan, written after 2–3
   real nights of protocol experience — do not write it speculatively.
4. **An open-problems board**: the ratified queue (writeup tasks,
   Hardy–Littlewood, parity barrier / Heath-Brown discussions, explicit12
   continuation, Night Cycle experiments) as blueprint-style cards so a
   fresh session can pick one up.
5. **Repo hygiene pass**: prune scratch/stale branches, verify the axiom
   audit runs clean from a fresh clone, CI (GitHub Action running
   `lake build` + `blueprint_lint.py`).
6. Decide: repo visibility/host, and whether the ledger dataset (artifact
   D) ships inside the repo or separately.

## 6. Sequencing

1. **Now (during the PRICE wave):** this pre-outline (done); the ledger
   taxonomy pass; method-stats compilation from flags.md + git log.
2. **Headline lands** → full ceremony → **MERGE (user decision, option (a))**.
3. **Post-merge week:** skeleton drafts of papers A and B; the README /
   ONBOARDING / CI items from §5; the taxonomy becomes anatomy-paper §3.
4. **Then the exploration sprint (§7)** — strictly timeboxed, in parallel
   with the writing (exploration is agent-heavy; writing is house-session
   work). It also road-tests clone-and-continue and feeds METHODS.md.
5. **Release** follows the sprint: papers + the exploration chapter + the
   repo with the open-problems board and the disclosed pre-registration.
6. **Post-release**: triage the remaining queue (further monuments,
   explicit12 continuation) informed by sprint findings and community
   uptake.

### Queue amendment (JYH-ratified 2026-07-14: demo over monuments)

- **Hardy–Littlewood is NOT done by us pre-release.** It is promoted to
  the FLAGSHIP item of the public open-problems board (§5 item 4): a
  fully blueprinted, pre-classified arc waiting in the repo. Rationale:
  a second monument adds little evidence (Chen already carried the
  capability update), while a well-prepared visible arc is the strongest
  adoption seed — the first outside group to land it validates
  clone-and-continue for us, with their name on it. What we don't prove
  is also a design choice.
- **The parity-barrier and Heath-Brown discussions are ABSORBED into the
  sprint**, not dropped: Heath-Brown = the design session for the Tier 3
  probe; parity = the frame for the Tier 1 atlas + Tier 2 GEH_min
  bracket.
- **The Night Cycle pre-loaded first nights change** from "H-L / parity /
  Heath-Brown" to the six pre-registered sprint questions.

## 7. The exploration sprint (JYH-ratified 2026-07-14: "harvest the low-hanging fruit, right now")

**The strategic argument.** The papers claim exploratory mathematics is now
cheap — but their evidence comes from verification work, where Chen was the
answer key. A skeptic can discount that. A *demonstrated* exploration —
questions posed without an answer key, explored, resolved or refuted in
days, under the same ledger discipline — removes the objection: it upgrades
the central claim from asserted to exhibited. And the asymmetry favors
doing it before release: pre-release, we hold exclusive access to the only
corpus where this is possible in analytic NT; post-release we are one team
among many. Harvest-then-release is the rational order. **Discipline:
strict timebox (~two weeks of Night Cycles), because "one more exploration"
is an infinite regress and the corpus's release value doesn't decay.**

### The demo design (the "big wow" — costs almost nothing extra)

**Pre-register the questions in the repo — PRIVATELY (JYH-ratified)**: a
signed commit stating "we pose these N questions; we do not know the
answers," BEFORE exploration begins. Private pre-registration preserves
both integrity and exclusivity: the commit hash is the tamper-evident
timestamp (optionally publish just the hash at sprint start); the commit
itself is disclosed at release, when anyone can verify the questions
predate the answers. Run the sprint under the Night Cycle protocol with the same
flags-ledger discipline (an exploration ledger). Report ALL outcomes —
resolved, refuted, open — with token and wall-clock costs per question.
"N pre-registered questions, k resolved, one refuted with a kernel-checked
witness, one open, D days" is a result no referee can wave away,
independent of how much gold turns up. **The process artifact IS the
demonstration.** Question selection is a user decision (which questions we
pose publicly commits us publicly).

### The three tiers and their distinct jobs (measure → map → probe)

**Tier 1 — calibration (known answer, unknown cost).** Not discovery:
the control group. Chen's second theorem (every large even N is p + P₂ —
same switch, same BV, different additive shape) measures the **marginal
cost of the next theorem** from the same machinery: if Chen-1 cost the full
arc and Chen-2 costs a few percent, that ratio is the empirical reuse
coefficient — a number nobody has ever measured, because nobody has had
the first theorem in reusable form. Secondary information: whether our
renderings were overfit to the (n, n+2) shape (finding that out is real
knowledge about what "reusable" means). Also p + 2k shifts. The M_k
delimitation atlas (M_k bounds for small k; Polymath8b's "H₁ ≤ 6 is
optimal for pure sieve arguments" as a formal theorem) sits between
calibration and discovery: folklore that has never been *stated*
precisely; the precision is the value.

**Tier 2 — interface theorems (the survey markers).** The result type:
*proofs-as-objects makes hypotheses measurable.* Informal conditionals are
stated with generous hypotheses because sharpening buys a human nothing;
formally, the proof tells you what it used. Deliverables: **GEH_min** —
the weakest precisely-stated equidistribution package that yields
H₁ ≤ 6 (converts a conditional result into an exact interface; tells
everyone attacking the conjecture precisely what would suffice; never
written down because it was never cheap to extract). The windowed-BV
variant we actually proved, stated cleanly and compared against the
literature (unrecorded ⟹ a minor-but-genuine new theorem; recorded ⟹
confirmed with explicit constants — reportable either way). The
explicit-constants audit (does any intermediate — BDH, the LS chain —
beat the published explicit literature?).

**Tier 3 — the frontier probe (the lottery ticket; timebox hardest).**
Tier 1's wall (the M_k atlas) and Tier 2's GEH_min bracket the corridor
where any twin-prime attack must live. Tier 3 probes it: formalize the
exact boundary of what our Chen machinery needs, then let exploration
sessions test perturbations — weight classes, switch structures — with
the refutation engine killing bad paths in hours instead of months. The
realistic best case is not "twin primes falls"; it is "a perturbation
whose obstruction is *different* from parity, stated precisely" — genuinely
new mathematical knowledge, of exactly the kind cheap exploration finds
and expensive exploration never gets to try.

### The six questions (JYH-ratified 2026-07-14; final pending pilot refinement of Q5 and the headline fixing Q2/Q6 references)

1. **T1 — Chen-2**: every large even N is p + P₂ (same switch, same BV,
   different additive shape). Calibration: the reuse coefficient.
2. **T1½ — the M_k delimitation atlas**: formal upper bounds for small k;
   Polymath8b's "pure sieve arguments cannot beat H₁ ≤ 6" as a theorem.
3. **T2 — GEH_min**: the weakest precisely-stated equidistribution package
   yielding gaps ≤ 6 (the explicit12 branch already carries Maynard
   variational machinery — the k=105 CertEval gates, mv_I/mv_J).
4. **T2 — the windowed-BV variant**: state exactly what we proved; sweep
   the literature; unrecorded ⟹ minor new theorem, recorded ⟹ confirmed
   with explicit constants. Reportable either way.
5. **T3 — the k = 2 boundary, constrained (TWO LEGS, JYH-ratified
   2026-07-14 after the pilot).**
   **(a)** For the marginal-CONSTRAINED enlarged k = 2 functional (the
   honest ε-trick class — P-A's OPEN 1), prove M₂^{[δ]} < 2 for ALL
   δ ∈ (0, 1] — the variational form of the parity expectation, never
   established at the proof level (the pilot's unconstrained bound covers
   only δ < δ₀ ≈ 0.4427) — or exhibit precisely where the retuned-CS
   route fails to use the constraint. Built-in R4 tripwire: a route
   "reaching 2" implies twins-under-GEH ⟹ definitional alarm.
   **(b, post-headline)** Within a precisely-defined perturbation class
   of the Chen razor, either close a P₁-razor from the landed level-½ +
   bilinear inputs (R4 alarm: implies twins) or land the obstruction as
   a theorem locating where parity bites machinery that already
   TRANSCENDS the pure sieve interface (Q6a's Selberg wall covers only
   sieve-interface consumers; Chen's switch injects bilinear information
   — this is the instance-level question only our corpus can pose).
   PRE-REGISTRATION PROTOCOL for (b): the commit states the question
   with the perturbation class as a NAMED PLACEHOLDER; the class is
   frozen in a follow-up commit after the headline (per R1/R3 — the
   class must be stated against the final H-package), BEFORE any (b)
   work starts; disclosed as such. Tamper-evidence preserved.
6. **T3 — THE PARITY PAIR**: (a) **the wall** — the Selberg-witness
   interface theorem: two instances of our BoundingSieve interface,
   agreeing in every field the sieve consumes (1 ± λ(n) weights), one
   sifted set containing primes and the other none — the parity barrier
   as a kernel-checked impossibility theorem about the interface itself
   (needs Σλ(n) = o(x), PNT-strength, in-corpus); (b) **the door** —
   TwinB_min: the Friedlander–Iwaniec-style extra axiom for the twin
   sequence, precisely stated ("here is exactly what remains, as a
   theorem"); the implication TwinB_min ⟹ twins kernel-checked as
   stretch. Honest calibration: this makes the problem precise, not
   solved — but precision at the frontier is the product our tooling is
   uniquely positioned to make.

(The explicit-constants audit runs as a side task, not a question.)

### The pilot (JYH-ratified: run an early T3 probe to calibrate before pre-registering)

**Disclosed and excluded**: the methods section reports "before
pre-registration we ran one pilot probe to calibrate budgets and stopping
rules"; its outcome does not count toward the pre-registered stats.
**Question**: probe the boundary of the landed M₂ ≤ 2 log 2 no-go — which
relaxations of the formal Maynard class move the bound? ((1+δ)-enlarged
support simplex, symmetry dropped, sign-indefinite weights; each ends as a
delimitation lemma, a refutation, or a precise open note.) **Runs NOW, in
parallel with the PRICE wave** (disjoint files, landed machinery only).
Timebox ~3 days. Deliverables: (i) the T3 experience report (executor
behavior on open-ended questions, honest stopping rules, where the human
decision points landed); (ii) calibrated T3 budgets for the sprint;
(iii) the mathematics, in whichever reportable form it takes; (iv) the
refined phrasing of Q5.

### Sprint parameters

Six pre-registered questions (above), two weeks, budgets per the Night
Cycle protocol as calibrated by the pilot, executors on Opus, all under
the exploration ledger. The exploration chapter tells the arc:
**measure (T1) → map (T2) → probe (T3)**, with costs attached to every
claim — and the parity pair as its centerpiece: the wall and the door.
