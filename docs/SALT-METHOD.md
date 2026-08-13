# THE SALT METHOD — canonical definition

**Captain-ratified 2026-08-12 (council session; revised jointly with the maestro from
the Captain's enumeration + the campaign's lived record). This document is the
method's constitution: the paper (Nature draft §5) states the creed; these are the
articles. Amendments are Captain-tier.**

## The creed (three commitments — the paper's §5 form, ratified 8/11)

1. **Truth is machine-checked only.** Every claim lands in the kernel, and nothing
   unverified accumulates into the record.
2. **Whatever the kernel cannot check is checked by structured opposition.**
3. **Human attention is the scarcest resource in the system**, spent exclusively on
   statements, designs, and rulings.

## REQUIRED (the method's invariants — tool-agnostic)

- **R1 — The five artifacts.** Given an objective, the agents produce five things: an
  implementation; a specification; a proof that the implementation meets the
  specification; tests — in the sharp form of ADVERSARIAL CONTROLS that prove the
  proof has bite (a mutation is valid only if it makes the goal false; a control that
  cannot fail is not a control); and SPECIFICATION CERTIFICATES — restatements S′ in
  simplified vocabulary whose IMPLICATION from the landed statement (⊢ S ⇒ S′) is
  KERNEL-PROVED, with the witness's kind declared. The direction is the safety
  property: the reader can only be reading something weaker than what was proved,
  never stronger; equivalence is the declared no-trade case. (Direction corrected
  from "equivalence" at the Captain's word, 8/12.) This holds at all levels, from project design to
  component design.
- **R2 — No claim without its checker.** No claim is admitted to the record without
  its checker: the kernel for mathematics (axiom-audited; no sorry on the record);
  the named instrument for measurements (the extractor command travels with the
  number); structured opposition for designs. Nothing unverified accumulates.
- **R3 — The ledger.** All design decisions are recorded in an APPEND-ONLY ledger,
  including human choices, producing a full record of activity — and its
  distinctive content is the ERRORS AND RETRACTIONS, amended at their source and
  recorded as first-class results alongside the wins.
- **R4 — Statement immutability.** No statement is ever weakened to admit a proof.
  Statement changes are design-tier acts, escalated to the top of the hierarchy,
  never taken by an executor.
- **R5 — Irreversible acts are human.** A small class of irreversible, outward-facing
  acts — submissions, purchases, publications — is reserved to human hands; the
  system's job is to reduce each to a prepared click, and stop.
- **R6 — Conditional objectives** *(added at the Captain's word, 8/12)*. Conditional
  objectives are allowed: a statement may name hypotheses it does not discharge,
  provided every hypothesis is named in the statement itself — never carried
  silently — and each carries one of two declared dispositions: (a) TO BE
  DISCHARGED — the hypothesis sits on the program's ledger as owed, with the
  expectation of a future kernel proof; or (b) OUT OF DOMAIN — the hypothesis marks
  a declared trust boundary with another discipline (for example, semiconductor
  physics, or a vendor's cell library), where the method's writ ends and the
  boundary is stated rather than owed. A program's final deliverable carries no
  undischarged in-domain hypotheses; conditionals are waypoints. (The closing
  sentence is the Captain's standing no-lingering-hypotheses law of 2026-07-26,
  folded in. Demonstrated instance: the bounded-gaps chain was built on a named
  Siegel–Walfisz hypothesis and the hypothesis was discharged the next day.)
- **R7 — Requirements are elicited, not assumed** *(added at the Captain's word,
  8/13; wording helm-drafted under his shape-ratification, amendable at his word)*.
  The referee has two ends it structurally cannot check: at the back, whether a
  proved statement means what a human thinks it means — guarded by R1's
  certificates; at the front, whether the specification is what the human wants.
  That front correspondence lives in the human alone, and the method is honest
  about the boundary and disciplined about how it is worked: (1) the vague want is
  WRITTEN DOWN FIRST, in doc form, never left in conversation; (2) the doc receives
  a STRUCTURED ADVERSARIAL REVIEW — inconsistencies, completeness, the population
  it covers, its negative space (what it deliberately does not do), suggestions
  ranked with benefits and downsides; (3) an INTERVIEW follows in which the human's
  answers are the ground truth being elicited, and the decisions are RECORDED — the
  transcript is the requirement's birth-case; (4) the revised English doc is the
  REQUIREMENTS ARTIFACT — the pre-registered source for specification and
  implementation, versioned and cited, with ACCEPTANCE CRITERIA registered before
  implementation begins; every later specification change traces to a requirement
  change. A spec written after the code is a description; a spec written before is
  a requirement. (The human's irreducible authority sits at exactly the two
  human-language ends — saying what is wanted, and reading what was proved — and
  the method's project is making everything between them run under the referee.
  Demonstrated instance: the jas requirements ritual, transcripts on that repo's
  record; the elicitation phrase is part of this article's record, below.)

  The elicitation phrase (the Captain's, extended at council 8/13 with the
  population, negative-space, and pre-registered-acceptance asks):
  > "Please read and understand these requirements. Analyze them for
  > inconsistencies and completeness. State the population this covers — the users
  > and uses it serves — and state the negative space: what is deliberately out of
  > scope. Propose the acceptance criteria we would register before implementation
  > begins: how we will know it is done. Make suggestions for improvements. Rank
  > your responses in priority from high to low, giving each a number. What are the
  > benefits? What are the downsides? Be ready for a deep dive into any of the
  > suggestions."

## ADVISORY (the reference configuration — what this program ran and measured)

- **A1 — One orchestrator.** A single master orchestrator agent on the top model
  class (Fable at the time of writing) performs the most complex design tasks and
  passes routine work to executors. It also owns the referee's own infrastructure:
  audit tooling is never owned by a seat it audits.
- **A2 — Executors.** Executors are the workhorse of the effort — building code,
  performing verification and proof, evaluating and refuting design options. Every
  task is classified by difficulty and priced BEFORE it is attempted; the
  classification determines which model tier may attempt it.
- **A3 — Budgeted attempts, loud exhaustion.** Attempts are budgeted small (this
  program ran ~3 serious attempts); exhaustion is RECORDED as a flag entry and
  escalated, never ground through. A recorded failure is the cascade working; a long
  grind is waste.
- **A4 — Exploration then refutation.** All major design phases have two parts: a
  design exploration phase, and a refutation phase that critiques the proposed
  design. Refutation is ADVERSARIAL BY ASSIGNMENT (a seat instructed to kill the
  design) and ITERATES UNTIL DRY. Acceptance criteria are PRE-REGISTERED before the
  artifact exists, so no checker writes its own bar.
- **A5 — Scheduled human interaction.** Human interaction is periodic and scheduled —
  this program held a daily council with recorded rulings.
- **A6 — Independent witness.** Every landing is verified by a second agent that did
  not produce it.

## Framing note (for the paper and for adopters)

REQUIRED states what the method IS — the invariants any implementation must keep.
ADVISORY states the configuration this case study actually ran and measured; other
configurations may satisfy the invariants differently, and the paper's n = 1 fence
applies to the Advisory tier, not the Required one.
