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


## 8. AMENDMENT 2 (8/5 night) — the LEG-1 HARVEST corrections
### Full dossier: docs/exploration/leg1-evidence-0805.md (740 ln, f5c80b9)

**THE NUMBERS ARE BIGGER THAN WE SAID** (all measured, commands in
the dossier): **652,312 Lean lines · 1,130 files · 19,564
declarations · 1,940 commits · 30 days** = 21,744 lines/day
sustained; +21.3% in the last five days. Zero `sorry`, zero
`native_decide`, zero home-rolled axioms across all 1,130 files.
**166 `#audit_axioms` build-time assertions naming 6,302 distinct
declarations.** 73 registry rows, lint-green. Papers: witness 20pp
with **172 statement-to-declaration citations**; flagship 17pp/152.

**⚠️ CORRECTION 1 — THE UNATTENDED CLAIM MUST CHANGE UNITS.**
The 21:00–05:00 night column is only **10.7%**; 77.2% of commits
land 07:00–18:59. *"Landed while the human slept" would fail the
first skeptic who runs `git log`.* The claim that IS true, is
stronger, and is checkable: **human-silence windows.** 14 days:
712 commits, 346,567 Lean lines inserted; **46.9% of commits (334)
and 193,289 lines landed inside a ≥1h silence window**; at ≥8h,
90 commits / 39,002 lines. **Best exhibit: 20h 56m of silence
(08-02 12:13 → 08-03 09:09) carrying 26 commits and 12,310 lines.
Longest unbroken run: 34 consecutive commits in 3h 20m with not one
typed human word.** SPEAK SILENCE WINDOWS, NEVER NIGHT HOURS.

**⚠️ CORRECTION 2 — the transcript record is contaminated, and it
flattered the OPPOSITE conclusion.** `task-notification` blocks are
injected with `role: "user"`, so naive counting showed 98.5% of
commits within 30 min of a "human message". Filtering (1,457
rejected + 214 slash-command echoes) moved the ≥1h figure from
**0.3% → 21.5%**. Any ledger we publish must filter these AND say
that it does — the methodology note is part of the credibility.

**⚠️ CORRECTION 3 — "13 waves on 8/5" is WRONG.** Measured: **11**
HB-Lemma-7 execution waves, or **15** Lean-landing waves counting
the morning constants work. Say 11 or 15, never 13. The day itself
is real: 45 commits, 8h 12m, 8,891 Lean insertions, 8 new files,
253 declarations. **"13 first-attempt landings" is UNVERIFIED** —
a flags.md claim, not derivable from git. Do not quote it.

**⚠️ CORRECTION 4 — THE HISTORY PURGE IS NOW ON THE CRITICAL PATH.**
**1,108 of 1,940 commits carry `the pre-remap address` as author email**
(known catch, fixed forward at a8fd364 on 7/21; history never
rewritten). Consequences: (a) salt's public release still gates on
the purge, as always; (b) **the purge rewrites 57% of the very
ledger that is leg-1's evidence.** RULING: **capture the ledger
NOW, from the current history, into a preserved artifact** (the
dossier already does this) — and note the triple's NEW public repo
is unaffected, born clean. The evidence can be SHOWN without
publishing salt.

**Overclaim hygiene:** the witness paper makes ZERO firstness
claims in 1,714 lines — good. All overclaim risk lives in internal
docs: `docs/RESULTS.md:170` states "first in a proof assistant"
flat where its own source `flags.md:3983` hedges it. Restore the
hedge before anything ships.

The dossier ends with **14 numbers safe to speak** and **11 items
marked DO NOT QUOTE** (incl. the stale 259/259 replay, the
"256 catches" counter-vs-count problem, and "zero wrong proofs",
which could not be verified). Read both lists before any room.

## 9. THE ORIGIN ARTIFACTS (JYH, 8/5 night) — both PUBLIC, both citable

- The IEEE conference paper: the high-speed ATM packet switch in CMOS VLSI.
- **US Patent 4,910,730** (patents.google.com/patent/US4910730A) — and
  the detail that matters: **it was TWO chips, Batcher and banyan
  separate**, with a pinout chosen so the fabric could stack in 3D.

**DESIGN CORRESPONDENCE (use this in the README):** the 1988
two-chip partition IS our proof partition. Chip 1 (sorter) =
the sorted-datum HYPOTHESIS, discharged by `Finset.orderEmbOfFin`.
Chip 2 (banyan) = `banyan_selfrouting`, PROVED, parametric in k.
The interface we assume is the interface he wired. **If we tape
out, we tape out chip 2 — the proved half.** The proof's shape is
not an arbitrary scoping choice; it is the original silicon's own
modularity, recovered 38 years later.

## 10. COUNCIL I RULINGS (8/6 morning) — THE SEAM DOCTRINE

**THE SEAM DOCTRINE (JYH-ratified, "now we have it"):** in the agent
era the compiler dissolves into the checked seam. Agents are
unverified stochastic translators (jas: 5 implementations, 5
languages); the field's old answer — translation validation (Pnueli
1998), proof-carrying code (Necula-Lee) — failed on human
proof-production cost. **Agents just paid its bills.** Per-instance
certification is the native verification mode of agentic
development. The campaign demonstrates the spectrum at three
altitudes: (1) AMORTIZED (the verified optimizer — prove once, run
millions); (2) PER-INSTANCE (the netlist equivalence — LibreLane
never trusted, every run checked); (3) THE FIVE-ARTIFACT LOOP
(spec/code/proof/certificates — code language fungible, the SPEC is
the only artifact whose language matters because it is the one a
human must read, and the certificate suite is how they read it).

**THE TOWER, retold (the toy-language answer):** the claim is DEPTH
not breadth — every seam closed, program → compiler → ISA → gates →
GDSII, kernel at each junction. CompCert = breadth on one seam;
nobody has depth on all. We say "miniature" first, then: name the
seam you distrust and we show its certificate.

**COMPILER PAIR (ruled):** leg 2 week-1 = the circuit-DSL verified
optimizer (committed, feeds leg 3). Week-2 stretch = the mini
software language → RV32I-subset code generator w/ simulation proof,
composing with the datapath into THE TOWER. (JYH's Caltech verified-
compiler research closes its own circle here.)

**FUNGIBILITY EXHIBIT (ruled, ~1 day, leg 2):** ONE spec of the
banyan router, SEVERAL deliberately different implementations
(iterative / unrolled / re-encoded), each proved equivalent to the
same spec — jas's observation converted from anecdote to theorem:
the certificate outlives every implementation.

**SYSTOLIC STRETCH (ruled, w/ the firewall):** a "systolic matmul
unit, after Kung–Leiserson 1978" — never the three letters — as
fleet-capacity stretch; int8 authentic; the multiplier proved
STRUCTURALLY (induction, not enumeration — the one real stone).
Two-chip tapeout echo noted (1988 had two chips; tiles are €70).

**MEASUREMENT PRE-REGISTRATION (ruled):** frozen TODAY before data
accumulates — (a) tokens by tier×project×task from session
transcripts (cache reported separately; tokens-not-dollars on
subscriptions; per-account attribution honest-if-weak); (b) JYH's
time in four categories: DIRECTING / REVIEWING / UNBLOCKING /
WATCHING — the campaign's dependency claim = the first three only,
counterfactual test "would the artifact exist without this touch";
WATCHING reported proudly as its own line (required ~40 min/day;
voluntary fascination: hours — the joy is evidence, not overhead).
No manual tracking; transcripts + published rubric + spot-audit.

## 11. FLEET RESOURCE LESSONS (8/6, day 1 — evidence-grade, keep honest)
- OOM #1 (morning): 5 seats × default parallelism on 64 GB; single
  Lean elaborations measured at 6-9 GB on heavy files. Fix:
  saltbuild.sh (fleet-wide lock + thread cap).
- OOM #2 (midday, averted): 49 bare lean processes, swap 37 GB — the
  lock covered `lake build` but not `lake env lean` audit runs, and
  in-flight subagents carried pre-rule briefs. Fix: the wrapper now
  fronts EVERY lean invocation; mid-flight executors re-briefed
  directly; seats re-pasted. **The lesson, ledger-worthy: locks must
  cover every door, not just the front one — and a rule change must
  reach the agents dispatched before it existed.** Both incidents
  cost ~zero work (lake resumes incrementally); both are honest
  entries for the unattended-operations story, not blemishes on it.
