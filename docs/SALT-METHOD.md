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
