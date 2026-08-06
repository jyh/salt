# THE TRIPLE — campaign freeze v1
### 2026-08-05 night. JYH's charge: math, code, VLSI — each
### kernel-checked, each agent-produced, largely unattended; the case
### made with numbers and concrete evidence in two weeks. No toys.
### Five accounts, round-the-clock. Window closes ~Aug 19.

## 0. THE ONE CLAIM

**The same method, the same fleet, the same referee discipline —
three domains, one fortnight, one person asleep.** Not three demos:
one machine, exhibited three times, with a ledger showing when each
artifact landed and who was awake.

Corollary claim (the one that matters to a discovery company):
verification is what lets an automated loop COMPOUND instead of
accumulate error, and it is now cheap enough to run unattended.

## 1. THE LEGS — asymmetric by design

### Leg 1 — MATHEMATICS: harvest, do not rebuild
Already won: 640K+ ln, 73 lint-verified theorems, 30 days, frontier
analytic NT, first formalizations, the Pearl + the Toll (paper in
final review), HB Lemma 7 assembled 8/5 in one day/night across 13
waves. **Deliverable: the evidence package** — the numbers, the
ledger, the axiom-audit posture, the two papers. Plus: keep the
fulcrum road RUNNING through the fortnight, because live landings
are the freshest evidence for the unattended claim.

### Leg 2 — CODE: a verified compiler (and it is load-bearing)
**A circuit DSL → synthesizable Verilog compiler with a
semantic-preservation proof.** The CompCert shape. Real by any
engineer's standard; personal-lane with no dependencies; and leg 3
CONSUMES it to reach layout. The interlock is the point: three
demos become one machine.
NOTE: no outside benchmark material is used — no
artifacts, no numbers, no shapes ported. SaltBench (the copyright-waiver filing filed,
approval pending) is NOT required for this leg and is not on the
critical path.

### Leg 3 — VLSI: the true build
FLOOR (must land): Batcher-banyan switch fabric proved in Lean
(parametric in N = 2^k) → emitted via leg 2 → OpenLane/sky130 (or
IHP) to real GDSII → **the gate netlist checked equivalent to the
proved design INSIDE THE KERNEL** (bitvector decision procedure
with certificate checking; NO native_decide, NO trusted external
equivalence checker).
STRETCH 1: a small RISC-V-subset core through the same chain
(RISC-V not ARM — ARM's architecture is licensed; the demo must be
publicly buildable and fabricable).
STRETCH 2: a shuttle submission if a window is open.
**Promise the chain, never the silicon.**

## 2. THE THROUGH-LINE — "sleep untroubled" is EXHIBITED, not argued

The artifact: a timestamped ledger — waves fired, waves landed,
axiom audits, walls honestly flagged — with the human's waking
hours overlaid. It already accumulates nightly (8/5: six agents,
six home, zero human hours). Two more weeks of it, charted against
wall-clock and dollars, IS the claim. Nobody else can show it.

## 3. CONSTRAINTS, NAMED

- NOT fuel (5 accounts, round-the-clock).
- **Sancho's design bandwidth** — every wave needs a frozen,
  refuter-attacked design first (13 first-attempt landings on 8/5
  came from exactly that). Mitigation: fork for parallel design
  blocks; refuter panels as workflows.
- **JYH's ratification cycles** — Aug 12 + day job + family.
  Mitigation: batched rulings with recommendations attached;
  routine forks ruled in flight under the standing order.
- **The VLSI toolchain unknown** — three scouts pricing now. The
  single fact that most changes the plan: whether the pinned Lean
  kernel checks bitvector certificates natively.

## 4. WHAT JYH OWES (small, and only this)

1. Protect Aug 12 — a live internal road outranks a sharper artifact.
2. Rule the public repo + name when the design arrives.
3. Hold the standing order so routine forks are ruled in flight.

## 5. THE DELIVERABLE

A public repo that builds end to end with one command, plus a short
evidence page: three legs, the numbers, the ledger, the fences
stated first. Every claim keyed to an artifact a skeptic can run.

## 6. FENCES (stated first, as always)

- No kernel decides physics, biology, or whether a design is worth
  building. The chain covers spec → artifact, and that is what
  makes the experiment trustworthy.
- Verified subsets are subsets: a RISC-V slice is not a CPU, and we
  will say which instructions.
- The layout tools stay unverified — we do not trust them, we CHECK
  their output. That is the contribution, and it is a different
  claim from "verified synthesis".
- Silicon is a stretch, and stated as one until a window is confirmed.


## 7. AMENDMENT 1 (8/5 night) — the BATCHER-SCOUT findings

**S1 IS ALREADY PROVEN.** `banyan_selfrouting`, parametric in k, 111
ln, sorry-free, 3 axioms, verified at the bytes by Sancho. Probe at
scratchpad/ProbeS1.lean — LIFT AS-IS into the repo. Leg 3a's heart
landed before the campaign formally began.

**⚠️ CRITICAL CORRECTION — `bv_decide` EMITS AN AXIOM.** Measured:
`#print axioms` on a `by bv_decide` goal returns
`[propext, Classical.choice, Quot.sound, <decl>._native.bv_decide.ax_*]`.
My proposed leg-3 route (kernel-checked netlist equivalence via
bitblasting + LRAT) **would have voided the no-new-axioms claim in
public.** The corrected plan:

- **FLOOR (ship it):** module-scale equivalence by `decide +kernel`
  — pure kernel reduction, 3 axioms, no native code. Measured
  ceiling: 2^16 configurations ≈ 6 min (bad CI citizen), 2^8 ≈ 0.2 s.
  So: modules with ≤ ~16 input bits, stated openly with the 2^n law.
- **The framing is BETTER this way**: we could have used the fast
  bitblaster and didn't, because it introduces an axiom. That is a
  demonstration of the discipline, not a limitation — and it is
  exactly the kind of detail that makes the rest believable.
- **STRETCH (leg 2's natural extension):** a VERIFIED certificate
  checker in Lean, so the fast route becomes admissible. This is the
  method eating its own dog food and it is a genuine contribution.

**S3 (Batcher's sorting network) is 800-1200 ln / 2-4 WEEKS with
ZERO mathlib support — DO NOT ATTEMPT.** Ship **S3′** instead:
`Finset.orderEmbOfFin` supplies the sorted datum, so the end-to-end
theorem ("any n distinct destinations, presented sorted, route
without conflict") lands in ~1 day. The deferred piece is labelled
honestly: we assume a sorter; mathlib provides one. **Decide this on
day 1, not day 10.**

**Representation, ruled:** ℕ carrier with div/mod and a DESCENDING
stage index (k does not appear in the main theorem; ℕ-subtraction
vanishes; `omega` survives to the endgame). `Nat.testBit` as the
public-facing facade so the statement reads as bit-routing. NOT
`Fin (2^k)`, NOT `BitVec`.

**Certificates, measured:** N=8 exhaustive over all configurations
0.2 s; N=16 pairwise-exhaustive 8 s (ship both); N=16 full 6m10s
(slow target or drop). The "obvious" bitmask optimization is SLOWER
— negative result, do not spend a day on it.

**Transplant:** `Salt/Tactic/AuditAxioms.lean` (127 ln, `import Lean`
only, same owner, personal lane) → the public repo verbatim. A
build-FAILING axiom assertion is the single highest-value import for
a repo whose selling point is the axiom posture.

**A genuine small result to ship:** the sharp hypothesis is not
"sorted + concentrated" but `dest b − dest a ≥ b − a`; the textbook
form follows in ~5 lines. Plus a minimal counterexample (k=2,
sources {0,2}, dests {0,1}) showing concentration is necessary —
credibility detail, put it in the repo as an `example`.
