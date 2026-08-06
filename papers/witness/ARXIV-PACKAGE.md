# arXiv package checklist — The Pearl and the Toll
### Prepared 2026-08-05 (Sancho); everything here is draft-for-JYH

## State
- main.tex compiles clean (two passes, exit 0) INCLUDING the ℓ-sweep
  (λ → ℓ in the width role; Liouville-only λ). Sweep is UNCOMMITTED
  pending the rest of JYH's review — finish review → batch commit →
  freeze the PDF.

## Metadata draft (JYH edits, then it's ready to paste)
- **Title**: The Pearl and the Toll: a Witnessed-Scale Two-Point
  Chowla Statement, Machine-Checked (— exact title from main.tex's
  \title; verify at freeze)
- **Authors**: as ruled — Jason Hickey; no affiliation (ruled 8/4);
  ORCID 0000-0003-0300-021X. The Claude collaboration line stays in
  the paper body as written (the abstract/intro states it); arXiv
  author list per JYH's ruling.
- **Primary category**: math.NT. **Cross-list**: cs.LO (the
  formalization content; math.LO alternative — JYH picks).
- **MSC**: as ruled at the 8/4 council (the ruled select).
- **License**: JYH picks (arXiv default non-exclusive license is the
  usual choice when a journal submission follows; CC-BY if he wants
  maximal reuse — check Forum of Math. Pi's policy: FoM Pi is open
  access and CC-BY-friendly, so CC-BY is safe).
- **Comments field draft**: "Machine-checked in Lean 4 over mathlib;
  every numbered statement names its Lean declaration and axiom
  audit. <availability sentence — see DECISION below>"

## THE ONE DECISION THE PACKAGE NEEDS (flagging, not deciding)
The paper is public the moment it posts; the salt repository is
private until the ratified gate (history purge + SaltBench
boundary). The Comments/availability sentence must say something
true about sources. Options:
  (a) "Formal sources available from the author on request; public
      release to follow." — cheapest, true, zero gate work.
  (b) Publish a frozen extract (the witness paper's dependency cone
      only) — real work + a mini-gate decision; NOT needed for
      arXiv; revisit at Pi refereeing.
  (c) Say nothing about sources — weakest; a formalization paper
      with no availability line invites the obvious question.
Recommendation: (a) now; (b) decided properly at the Pi stage
alongside the show-vs-describe ruling already in the register.

## Endorsement (the blocking item — JYH searching)
Natural candidate shapes, JYH's choice and JYH's words entirely:
- The formalization∩analytic-NT overlap — people who would actually
  want to read this: the PrimeNumberTheorem+ project circle (e.g.
  A. Kontorovich; T. Tao — whose theorem the toll prices, and the
  note "your entropy-decrement argument, kernel-checked, with the
  tower's cost made explicit" is honest and specific).
- Former Caltech/Cornell colleagues active in math.NT.
- Mechanics: arXiv → New submission → it names the endorsement
  requirement and generates the request link/code per category;
  endorser needs recent math.NT authorship. The ask travels well
  with the abstract attached — it is genuinely interesting.

## Sequence to submission
1. JYH finishes the Witness review (tonight, as planned) → batch
   commit (ℓ-sweep + review notes) → freeze PDF.
2. JYH sends endorsement ask(s) with the abstract.
3. Metadata + availability sentence ruled (10 minutes, above).
4. Endorsement arrives → submit same day. Target: this week.
5. On posting: update ready-response "SENDABLE TODAY" (the paper
   joins the list) + the Pi submission follows on its own clock.
