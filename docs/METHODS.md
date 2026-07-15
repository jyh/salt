# THE SALT METHOD — how this project does mathematics

*Fable + human, 2026-07-12. This document codifies the working methods
developed over the salt project's arcs (Brun → BV → twinbar → P0/P1 →
SW → Chen). It is the repo's self-description: a new session reading
only this file and `CLAUDE.md` should be able to run either method.
The evidence that the methods work is `docs/blueprints/flags.md` — at
this writing, 27 design errors caught before any proof was built on
them, and 0 wrong results ever landed.*

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
   verification by a different method). The gate's job is to break the
   blueprint. Fold catches; re-freeze; only then dispatch.
4. **Waves.** Class-B/C nodes to executors with rich briefs: the
   frozen target verbatim, the landed inputs to READ FIRST, the
   expected mechanism as a sketch THE PAPER OVERRIDES, sanctioned
   **PB-floors** (partial deliverables that are honest standalone
   artifacts), and the budget. New files only; the designer owns
   wiring and aggregates.
5. **Verify → commit → ledger.** Per landing: sorry/native_decide
   grep, full build with `#audit_axioms` in-build, axiom set at most
   `[propext, Classical.choice, Quot.sound]`, statement fidelity
   against the freeze. Update the node's blueprint row and the flags
   ledger in the same commit. House commit style:
   `<track> <node>: <name>` + model/attempt line.
6. **Floors close same-day where possible.** A floor is a contract to
   dispatch the follow-on node, not a place to rest.

**Doctrines that earned their place** (each traceable to a catch):
transcribe-first (#16, #24); statement-freeze + STOP-AND-FLAG (#17,
#22, #25, #26); the budget ledger (#21, #23); decomposition errors are
still errors — hypothesis lists are part of the freeze (#18, #19);
interface hypotheses beat improvised statements (every floor);
carriers must carry enough — an operating-point map that forgets its
cutoff blocks the mathematics (#27).

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
     load-bearing; a research memo without it is not done.
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

## Naming

**The Salt method** (ratified 2026-07-12): the umbrella discipline —
every claim either passes a referee or carries a loud flag. Its two
faces are the proving method and the research method, entered by
their invocation phrases; its spine is the loop contract; its
evidence is the flags ledger. (Runner-up names on file for the
writeup's discussion: *the Cascade*, *kernel-trust*,
*freeze-and-flag* — each names a component; *Salt* names the whole.)
