# THE SALT METHOD — how this project does mathematics

*Fable + human, 2026-07-12; revised 2026-07-15 at the completion of
the Chen arc (`chen_headline` — Chen's theorem, unconditional,
kernel-checked). This document codifies the working methods developed
over the salt project's arcs (Brun → BV → twinbar → P0/P1 → SW →
Chen). It is the repo's self-description: a new session reading only
this file and `CLAUDE.md` should be able to run either method. The
evidence that the methods work is `docs/blueprints/flags.md` — at
this writing, 78 design errors caught before any wrong proof could be
built on them, and 0 wrong results ever landed. The 2026-07-15
revision adds Part III, the integration doctrine — the lessons of the
Chen endgame, where the last twenty catches (#59–#78) were all
interface defects and forced the method's largest upgrade.*

There are two methods. They share a spine — the **loop contract**, the
tier cascade, and the ledger discipline — and differ in one thing:
**what referees success.**

- The **proving method** exists because we have a mechanical referee:
  the Lean kernel plus the in-build axiom audit. No wrong result can
  survive, so delegation can be aggressive and the loop can run
  autonomously.
- The **research method** is what remains when the referee is removed:
  success is judged, not checked. Its structure exists to substitute
  verification *rituals* for the missing referee, and decisions for
  the missing QED.

Each method is entered by an **invocation phrase**. The phrase is not
decoration — it sets the contract for the whole session that follows:
what a wave produces, how it is verified, and what "done" means.

---

## Invocations

| You say | Method | Register | The freeze | Done means |
|---|---|---|---|---|
| **"Let's prove X."** | Proving | — | the STATEMENT of X, from primary sources | kernel-checked, axiom-clean, committed |
| **"Let's investigate Q."** | Research | tight | the QUESTION Q | a verdicts memo with precision guards |
| **"Let's brainstorm A."** | Research | mid | the AREA A | a ranked option list with feasibility calls |
| **"Let's play."** | Research | open | only the corpus | candidate directions worth freezing later |

The three research registers are one method at decreasing constraint,
not three methods. Play discovers areas; brainstorm turns an area into
questions; investigate turns a question into verdicts; proving turns a
statement into a theorem. The twinbar flagship — the first
machine-checked impossibility theorem about a sieve method — was born
in the play register ("what would really set this apart is new math"),
which is the canonical demonstration that the pipeline runs end to end.

---

## The shared spine: the loop contract

**This section is the essential one.** Both methods run inside the
same loop, with the same role split and the same stop conditions.

**Roles (the tier cascade — full policy in `docs/MODEL_POLICY.md`):**
- The **designer** (Fable-tier, or the human) owns: blueprints,
  statement/question freezes, difficulty classification, adversarial
  gates, verification of every landing, commits, and the ledger.
  Statement changes are designer-tier ONLY (Iron Rule 1).
- **Executors** (Opus-tier) own: one node each, from a rich
  self-contained brief, in a new file, with no commits and no edits
  outside their file. They report; they never merge their own work.
- The **human** owns: what to work on, ratification of designs and
  budgets, and every merge to main. Merges are never autonomous.

**The wave loop:**
1. The designer freezes the target (statement or question) and gates
   the design adversarially BEFORE any executor sees it.
2. Independent nodes dispatch in parallel waves; dependent nodes wait.
3. Every landing is verified by the designer (proving: sorry-grep,
   full build, in-build axiom audit, statement fidelity; research: the
   verification rituals below), then wired, documented, and committed
   — docs in the SAME commit as the work.
4. The next wave dispatches immediately. The loop continues without
   asking permission.

**Stop conditions** (the loop stops for exactly three things):
- **done** — the frozen target is landed;
- **blocked** — a flag was raised that needs a designer- or human-tier
  decision;
- **genuine user input** — a fork only the human can choose (a merge,
  a budget, a change of target).
Everything else — errors, retries, floors, follow-on nodes — is the
loop's own business. The human is briefed at wave boundaries, not
consulted at them.

**Give up early, loudly** (Iron Rule 4, both methods): a budgeted
number of serious attempts, then a precise flag in the ledger and
movement to the next node. A recorded failure is the method working.
Executors who cannot prove a statement as frozen must STOP AND FLAG —
never improvise the statement. Six of our 27 catches were surfaced by
executors holding this line, including one machine-checked
counterexample to a designer-frozen definition (#26) and one erratum
in the published source itself (#24).

---

## Part I — The proving method ("Let's prove X.")

The full per-node rules live in `CLAUDE.md`; this is the arc-level
method.

1. **Recon.** Scout the routes (parallel independent scouts when the
   route is genuinely open). Identify the primary source. Inventory
   what the corpus and mathlib already provide.
2. **Freeze.** Transcribe the mathematics from the primary source AT
   PAGE-IMAGE LEVEL (pdftotext lies about formulas — catches #16, #24
   were both invisible in extracted text). Freeze every statement
   O-free with explicit constants, every hypothesis enumerated, every
   operating point pre-computed with margins. If constants are razor
   (< a few percent), freeze a **budget ledger** first: every slack
   site gets a cap, the caps sum under the margin, and every executor
   landing is checked against its row (the Chen C0 doctrine).
3. **Gate.** Run an adversarial gate on the blueprint BEFORE wave 1:
   independent lenses (statement fidelity vs sources, budget
   arithmetic, interface fit against the landed corpus, numeric
   verification by a different method, and — post-Chen — JOINT
   SATISFIABILITY of every hypothesis package an operating point must
   discharge). The gate's job is to break the blueprint. Fold catches;
   re-freeze; only then dispatch.
4. **Skeleton (added 2026-07-15 — see Part III).** Before component
   waves, land the refinement skeleton as kernel-checked mathematics:
   the headline theorem reduced to a small set of named hypothesis
   bundles, each **anchored at the operating witness** (the concrete
   z/y/D/Q/threshold family), not at free parameters, and each
   carrying a **satisfiability witness** — a compiled example that its
   premise set is jointly inhabitable and its output feeds its
   consumer slot-exactly. The bundles are the wave plan; sibling
   bundles parallelize for free.
5. **Waves.** Class-B/C nodes to executors with rich briefs: the
   frozen target verbatim, the landed inputs to READ FIRST, the
   expected mechanism as a sketch THE PAPER OVERRIDES, sanctioned
   **PB-floors** (partial deliverables that are honest standalone
   artifacts), and the budget. New files only; the designer owns
   wiring and aggregates. Model routing is EXPLICIT per dispatch
   (executors on the workhorse tier; never by inheritance).
6. **Verify → commit → ledger (the ceremony).** Per landing:
   sorry/native_decide grep, wiring into the audited aggregate, full
   build with an EXPLICIT exit-code check (never the tail of piped
   output — a pipe once masked a broken push), `#audit_axioms`
   in-build, axiom set at most `[propext, Classical.choice,
   Quot.sound]`, statement fidelity against the freeze. Update the
   node's blueprint row and the flags ledger in the same commit. House
   commit style: `<track> <node>: <name>` + model/attempt line. The
   executors get to be fearless because the ceremony is paranoid.
7. **Floors close same-day where possible.** A floor is a contract to
   dispatch the follow-on node, not a place to rest.

**Doctrines that earned their place** (each traceable to a catch):
transcribe-first (#16, #24); statement-freeze + STOP-AND-FLAG (#17,
#22, #25, #26); the budget ledger (#21, #23); decomposition errors are
still errors — hypothesis lists are part of the freeze (#18, #19);
interface hypotheses beat improvised statements (every floor);
carriers must carry enough — an operating-point map that forgets its
cutoff blocks the mathematics (#27); estimate-vs-statement divergence
— a proof that needs less than its statement demands, or a statement
that demands the impossible, is a catch even when everything
typechecks (#47, #64, #66, #69); satisfiability witnesses at freeze
time (#65, #68, #71 — see Part III); constants and thresholds must be
UNIFORM — a per-instance existential or an x-dependent parameter
bound before its `∀` detonates at assembly (#76's uniform-K rebuild
at HCOUNT-3; #77's arg-free restatements at FIN-A3); honest re-derivation beats a sketch — every
aggregate constant is recomputed when instantiated, and nine orders
of magnitude of drift is survivable only if the consumer was built
parametric (#74).

---

## Part II — The research method ("Let's investigate / brainstorm / play.") — v0

*Marked v0: prototyped this project as the recon layer of proving
(the parity-frontier memo, the conjectural-landscape memo, the Chen
three-scout recon, the Mertens tools inventory) but not yet run as a
first-class activity. The structure below is what those prototypes
converged on.*

1. **Freeze the question** (or area, or — for play — nothing but the
   corpus inventory). Written down before any scout launches, with the
   same discipline as a statement freeze: what would count as an
   answer, and what is explicitly OUT of scope.
2. **Scout fan-out, independent lenses.** Parallel scouts that cannot
   see each other's findings, each with a different search modality
   (by-source, by-era, by-technique, by-counterexample). Sources open;
   primary PDFs over surveys over folklore; expositions only when the
   primary is paywalled, and SAY SO.
3. **Verification rituals** (the kernel substitutes — use all that
   apply):
   - **verbatim quoting** checked against page images, never from
     memory;
   - **numeric experiment before conjecture** — compute the margin,
     the integral, the counterexample candidate, at high precision by
     TWO independent methods before any claim rests on it;
   - **cheap formal probes** when the question is feasibility — a
     kernel-time measurement beats an estimate (the CertEval pattern);
   - **the COULD-NOT-VERIFY ledger** — every claim that rests on a
     secondary source, an abstract, or an unfetchable original is
     listed as such, verbatim, in the deliverable. This section is
     essential; a research memo without it is not done.
4. **Adversarial distillation.** A judge pass over the scouts'
   findings before synthesis: what's missing, what conflicts, which
   quotes don't survive re-checking. (The gate, pointed at claims
   instead of blueprints.)
5. **The deliverable is durable or the expedition didn't happen** (the
   PB-floor analog): a memo with **verdicts**, **precision guards**
   (exact wordings future quoters must respect), and the
   could-not-verify appendix — committed to `docs/blueprints/`. For
   brainstorm: a ranked option table with feasibility calls against
   the corpus ("what do our tools make cheap?"). For play: candidate
   directions, each with the invocation it would graduate to.
6. **Iterations end in decisions, not QEDs**: every direction is
   marked **pursue** (freeze it and invoke a method), **park** (record
   why and what would revive it), or **kill** (record the
   counterexample or blocker). Undecided directions are the research
   method's version of `sorry` — not allowed in a finished expedition.

**The graduation path**: play → brainstorm → investigate → prove is
the intended pipeline, but any stage can be entered directly, and an
investigation that hits a provable statement should say so and stop —
freezing early is cheaper than researching past the answer.

---

## Part III — The integration doctrine (2026-07-15, from the Chen endgame)

*The Chen arc's second half — from the certified razor to the landed
headline — took as long as its first half, on a phase the blueprint
had estimated at three nodes. It produced twenty catches (#59–#78),
every one an INTERFACE defect: hypothesis packages individually true
and locally checkable but jointly uninhabitable, carriers that two
correct subsystems disagreed about, constants quantified in the wrong
scope. None was visible in the classical literature, because
classical proofs discharge the entire integration phase with one
sentence: "now take x sufficiently large." This part codifies what
that sentence actually costs, and how to pay it early and in
parallel.*

**III.1 — The two empirical laws.**
- *Component construction is predictable; integration is where the
  estimate variance lives.* The Chen build phase ran to plan; the
  "glue" ran 10× its estimate. Budget them as different lines.
- *Integration cost scales with the number of subsystems sharing an
  operating point* — not with proof length. P0/P1 (one sieve): no
  tail. SW (a linear chain): small tail. BV (two systems): seven
  pre-execution catches. Chen (~seven subsystems at one shared
  operating point): a tail equal to the build.

**III.2 — Premise latency, the governing metric.** Define the premise
latency of a decomposition as the time between FREEZING its
hypothesis rows and first ATTEMPTING them at the target instance.
Vacuous and interface-mismatched lemmas typecheck in any prover —
`x<0 → x>2 → P` is as provable as its honest cousin
`x<0, x>2 ⊢ ⊥`, and no kernel objects — so nothing in the logic
surfaces an uninhabitable decomposition until someone instantiates
it. In goal-directed refinement (the PRL tradition) latency is ~0 by
construction: subgoals are born from the live goal, at the live
instance, and a bad decomposition is exposed as immediate stuckness.
In library style — free-parameter lemmas, promissory "the glue
discharges this" notes — latency is unbounded, and the integration
tail is the accumulated debt coming due at once. The Chen ledger is
the measurement: rows frozen 15 hours (catch #64) to several days
(catch #66) before first instantiation, each surfacing as a
terminal-node catch.

**III.3 — The remedy: witness-first refinement with library
execution.** Neither pure style suffices at this scale. Top-down
refinement gives instance-anchored decomposition but is ergonomically
hostile in a file-based prover (one monolithic term; no parallel
executors; no incremental commits). Library style gives parallelism
and per-node ceremonies but detaches lemmas from their instance. The
synthesis, proven in the Chen endgame's final ten hours (the
`chen_headline_of_A3_ledger` skeleton, after which per-catch repair
cost visibly dropped and the frontier became two enumerable leaves):

1. Construct the OPERATING WITNESS first — the existential near the
   root of the goal is refined before any component work.
2. Land the SKELETON as kernel-checked mathematics: the headline
   reduced to named hypothesis bundles STATED AT the witness.
3. Every decomposition ships a SATISFIABILITY WITNESS when frozen — a
   compiled example that its premise set is jointly inhabitable and
   that its output feeds its consumer character-for-character (the
   anti-vacuity discipline; in refinement-calculus terms, the extract
   content that proof-irrelevant `Prop` discards). A would-be witness
   that implies something famously open is a DEFINITIONAL ALARM, not
   a result (the F≡1 episode).
4. Fill bundles by parallel library waves against the frozen,
   witnessed interfaces — sibling bundles are independent by
   construction.

The meeting line between forward-built supply and backward-refined
demand becomes many small early meetings instead of one large late
one — which is exactly where the interface-scaling law stops hurting.

**III.3′ — The witness ladder (when the existential is hard).** The
doctrine above says "construct the operating witness first," but for
`∀x ∃y P(x,y)` the witness is often hard — and sometimes provably
unknowable (Siegel's ineffective constant sits inside our own SW
gate). Stated honestly, witness-first means **witness-accountability
first**: what must exist from day one is not `y` but a single live
object that stands in for it — a unified constraint store with a
current satisfiability certificate — plus the rule that no
decomposition freezes without being charged against it immediately.
The failure mode this kills is never "we lack the witness"; it is
"constraints on the witness live in five files and have never met"
(catch #64 exactly: two D0 rows, each fine, first placed in the same
store fifteen hours after freezing — jointly empty). Climb only as
high as the problem permits:

- **Rung 0 — name it.** Skolemize; turn witness-finding into
  constraint accumulation against ONE ledger; re-verify the store's
  satisfiability at every freeze. (The analyst's "choose the
  parameters at the end," made disciplined.)
- **Rung 1 — solve it numerically.** The satisfiability check needs
  machine precision, not a formal term: feasibility tools (LP for
  budget ledgers — the 1/200 share budget was one; interval
  arithmetic for margins; numeric optimization for variational
  witnesses) gate the freezes, and the formal proof later CERTIFIES
  the solver's answer (the panel-certificate pattern: c̄'s 600
  panels, the D0-window witness).
- **Rung 2 — commit coordinatewise, hardest last.** The witness
  tuple need not arrive atomically: freeze cheap coordinates early,
  keep hard ones symbolic-with-constraints, and take the threshold as
  "max of everything, chosen last." Most interface defects are
  detectable from the rows alone, before any final coordinate exists
  (#64, #66, #69, #71 all fell this way).
- **Rung 3 — when unconstructible, consume instead of construct.**
  For ineffective or purely classical existentials, use the ∃ through
  its elimination rule only: destructure first, keep every consumer
  UNIFORM in the unknowable value, absorb the one concrete need into
  a function of the destructured constant (the x₀(K) pattern, used
  six times in the Chen endgame). Triage every witness coordinate as
  construct / solve / consume, and shape interfaces accordingly —
  catch #77 was a triage failure.
- **Rung ∞ — when possibly nonexistent, race search against
  refutation.** If the constraint region may be empty, that is
  research: run numeric witness-search and adversarial emptiness
  probes in parallel, either outcome a first-class deliverable. The
  twinbar no-go is this with the sad ending made rigorous (the
  hoped-for weight provably doesn't exist); catch #64's emptiness
  certificate is the same event at micro-scale, and it DROVE the
  repair. Emptiness proofs are not failed hunts; they are the map of
  the wall.

(In proofs-as-programs terms: when the extract is too expensive to
compute eagerly, make it lazy — the constraint store is the thunk's
accumulated environment, forced once at the end.)

**III.4 — Quantifier scope is architecture.** The endgame's last
catches were all binding-structure defects: constants existentially
quantified per-instance where a fixed constant was needed (#76's
uniform-K rebuild), parameters bound before a `∀x` making thresholds
un-extractable (#77's arg-free restatements). Rule: every supplier
whose consumer must destructure it exposes its constants and
thresholds OUTSIDE the quantifiers its consumer instantiates —
"destructure all existentials first, choose the working threshold
last" is only executable against arg-free suppliers. Check this at
statement-freeze time; it is invisible to the kernel and expensive at
assembly.

**III.5 — Catches are the product.** A catch — a true estimate
wearing a false statement, an uninhabitable package, a mismatched
carrier — is the method working. File it with both sides' values;
adjudicate the repair (additive fixes under explicit warrants
preferred — of the twenty endgame catches, none required demolishing
landed work); never let one become a wrong proof. The ledger's
taxonomy (local defects in the build phase; interface defects in the
integration phase) is itself the empirical map of where correctness
lives in a classical proof — the project's central scientific
artifact, producible by no other process we know of.

**III.6 — The method in one breath.** *Refine the goal backward into
witness-anchored, satisfiability-witnessed bundles under adversarial
gates; build forward in parallel against those frozen interfaces with
paranoid per-landing verification; let a single designing mind own
statements and a kernel own truth; record every failure precisely;
and spend your surprise budget where the subsystems meet, because
that is where it will be spent whether you plan for it or not.*

---

## Naming

**The Salt method** (ratified 2026-07-12): the umbrella discipline —
every claim either passes a referee or carries a loud flag. Its two
faces are the proving method and the research method, entered by
their invocation phrases; its spine is the loop contract; its
evidence is the flags ledger. (Runner-up names on file for the
writeup's discussion: *the Cascade*, *kernel-trust*,
*freeze-and-flag* — each names a component; *Salt* names the whole.)
