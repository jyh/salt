# FIRST-REFUTER CRITERION — compiler's L2 restatements (1f83b9a · 1a32c1d · a8582b8)
# math seat, life 10. WRITTEN BEFORE OPENING ANY DIFF. Timestamped by the commit that carries it.
#
# ⚠️ CONTAMINATION DECLARED: I read compiler's 07:32 suspected-weakness note during the
# boot order (FLEET tail) BEFORE writing this. Their four items are therefore IN MY HEAD.
# Every line below is marked [MINE] or [THEIRS] so the pass can be discounted correctly.
# Compiler's own standard: a finding inside their list is worth less than one outside it.

## SCOPE — silicon pinned this; I redo NONE of it
DISCHARGED ALREADY (do not re-run): kernel witness per changed file (silicon MEAS,
tree-pinned) · hub-wide integration (maestro covering builds) · four retired names cease
to exist, no aliases (silicon rider ①) · audit ticks 26/26 verified exact.
MINE = THE MATHEMATICS OF THE THREE RESTATEMENTS ONLY.

## PRE-REGISTERED PASS/FAIL — I commit to these verdicts before looking

### C1 [MINE] THE RESTATEMENT-MEANING TEST (my own seat's law, decQ_encD hazard)
Four names were RETIRED and three theorems RESTATED. The retirement is checked.
THE RESTATEMENT IS NOT. For each of the three:
  would a citation written BEFORE the restatement still be TRUE of the new statement?
FAIL if any restated theorem KEPT its name while changing what it asserts.
  (retirement fails loudly at a grep; restatement resolves SILENTLY, forever.)

### C2 [MINE] NON-VACUITY OF THE NAMED BOUNDARY
1f83b9a "NAMES the fragment boundary". A boundary predicate can be:
  (a) unsatisfiable  ⇒ the three theorems are vacuously true
  (b) always true    ⇒ the boundary names nothing and the theorems are unrestricted
FAIL unless BOTH are excluded by exhibited witnesses: something IN the fragment and
something OUT of it, and the out-witness must make the conclusion actually FALSE.
  ⇒ this is my seat's mutation-control law: unreachable-by-one-route is NOT falsity.

### C3 [MINE] DEMAND SIDE — WHAT CONSUMES THESE THREE?
Standing law of this seat: measure what the SPEC REQUIRES before crediting what exists.
For each restatement: name its CONSUMER. A boundary theorem whose consumer needs the
CONVERSE is a theorem that will not discharge the obligation it was written for.
FAIL if any of the three has no consumer and no spec line demanding it.

### C4 [MINE] STRENGTH LEDGER — DID THE RESTATEMENT WEAKEN?
A restatement onto a named boundary ADDS a hypothesis by construction. Is the old
(unrestricted or differently-restricted) content still available, or was it LOST?
FAIL if strength was shed silently — i.e. shed without the commit or docstring saying so.
  (my own life-9 precedent: Thm 3.3's height binder retirement was disclosed in a remark;
   that is the standard.)

### C5 [THEIRS, item 4 — restated in my vocabulary] THE ASYMMETRIC BOUND OFF-BY-ONE
whileFits uses 2048 backward / 2047 forward. Compiler says no certificate sits near the
boundary. TEST: is the asymmetry DERIVED from the encoding, or ASSERTED? If derived,
where; if asserted, an off-by-one in either direction is undetected by every passing
certificate. FAIL if asserted with no derivation and no boundary-adjacent witness.

### C6 [THEIRS, item 2] encodeOK COVERS REGISTERS ONLY
Check step_mem_eq / step_trapped_eq actually cover the TWO NEW BEQs, not the five arms
they were written for. FAIL if a new constructor is outside their induction.

### C7 [PRE-REGISTERED BY MY PREDECESSOR, bank item ②] THE 99999 CONTROL
branchFree_is_necessary_not_sufficient's witness is pinned to the CONSTANT 99999.
Does the witness survive if the immediate bound moves? A control pinned to a constant
tests a POINT, not a PROPERTY. FAIL if the theorem's content depends on 99999 exceeding
a bound that is itself a movable definition, with no lemma tying them.

### C8 [PRE-REGISTERED, bank item ③] REACHES BESIDE FROZEN L1
The Reaches-shaped loop theorem lands beside FROZEN L1 content (§4b). FAIL if it
restates or shadows frozen content rather than sitting beside it.

### C9 [MINE] THE AUDIT-LINE GATE — my own life-9 defect, hunted in another's hands
Every declaration a commit introduces gets its roll-call line IN THE SAME COMMIT.
A declaration with NO audit line is SILENT, not failing; a green build says nothing
about it. FAIL any new declaration in the three commits with no roll-call line.
  ⇒ I earned this one by shipping two unaudited declarations on 08-10. Hunting my own
    class in someone else's hands is the seat's stated conduct.

## WHAT I EXPECT TO FIND (recorded so I can be scored, not so I can be right)
Highest prior: C9 and C2. C9 because it is mechanical and recently bit me, so I know its
shape. C2 because "NAMED the boundary" is exactly the phrase under which vacuity hides.
Compiler bets on their item 3 (emitter layout untested under nesting) — that is a
TESTING gap they already disclosed in §7, not a false theorem, so by my C-list it is
NOT a refutation. I say so now, before reading, so I cannot be seen to have moved the bar.

---

## VERDICT AS RUN — 2026-08-11 07:39 PDT (added after the pass, criterion above UNEDITED)

C1 PASS on theorems · ONE DOC FINDING: WhileScheme.lean:8 carries a present-tense
   sentence FALSE since a8582b8; the correction is at :434 and says so deliberately,
   but there is NO POINTER AT :8. Amend-in-place satisfied; DISCOVERABILITY is not.
C2 PASS — non-vacuity EXHIBITED both directions (`fragment_now_includes_while`,
   `cause_outside_the_fragment_is_now_ite_only`), decide +kernel, not asserted.
C3 PASS — consumers named: BlockCalc:212/214, CompileS:678, WhileSim:67 (assign
   lifts the restatement verbatim in ONE line — the restatement paid for itself).
C4 PASS ABOVE STANDARD — the old statements are FALSE, not weakened, and the commit
   says WHY (forward quantifies over every output; while emits two BEQs).
C5 ⛔ NOT RUN — whileFits 2048/2047 asymmetry, derived or asserted? OWED.
C6 PASS — step_mem_eq/step_trapped_eq are ∀ (i : Instr) by `cases i`; a new
   constructor cannot escape them silently. Compiler's item 2 is unfounded BY SHAPE.
C7 PASS — and stronger than pre-registered: the 99999 control is DIFFERENTIAL
   (same reg/d/Γ/head as `witness_chain_discharged`; only the expression differs),
   so the `none` is attributable to the constant. Failure mode is LOUD.
C8 PASS — L1 not re-proved.
C9 PASS — see the extractor `scripts/audit_gate.sh`, shipped per the count law.

### THE INSTRUMENT FINDING — the extractor's phantom
`audit_gate.sh` and its file-level sibling read 24 decls vs 23 audit names in
WhileScheme.lean. ONE COMMAND FROM PUBLISHING "one declaration is unaudited".
It was the extractor: line 81 is a DOC-COMMENT sentence beginning with the word
`theorem`, and an anchored `^theorem ` ate prose shaped like structure.

    1a32c1d  raw 27 · phantom 1 · REAL 26 · audit 26   (compiler's 26/26 EXACT)
    a8582b8  raw 24 · phantom 1 · REAL 23 · audit 23   (3 retired, 3 audit lines
    HEAD     raw 24 · phantom 1 · REAL 23 · audit 23    went with them, lockstep)

⇒ THE RULE THAT CAUGHT IT IS MECHANICAL, NOT CAREFUL: never publish a count
  without naming the member. Naming forced the word `because` into the output,
  and a declaration called `because` is not a declaration.
