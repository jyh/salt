# PRE-REGISTRATION — sprint 2: the limits of the method (DRAFT, pending JYH sign-off)

**Status: DRAFT 2026-07-15. Becomes THE REGISTRATION on JYH
ratification + the signing commit** (same protocol as sprint 1: the
hash of the ratifying commit is the tamper-evident timestamp; the
repository is private at registration; disclosed in full at release).
**Not effective until sprint 1 closes** (chen_goldbach lands or its
final honest flag is ceremonied) and JYH signs off, per the ratified
direction (the exploration ledger, 2026-07-15 ~20:40).

**Declaration.** Sprint 1 tested the instrument where answers were
known or reachable; it went six for six. Sprint 2 deliberately tests
the two limits sprint 1 did not touch, and we commit in advance to
reporting ALL outcomes with costs — including, and especially, the
failures. The two limits are registered as separate tracks with
separate success criteria, because they measure different things:

- **Track A measures depth**: can the method conquer, in ~1.5 days, a
  classical arc that is genuinely deep, absent from mathlib, and
  already DEFEATED one recon (the Rb-4 verdict-D)?
- **Track B measures the frontier**: on problems whose solutions are
  NOT known, what does the method actually produce? The registered
  claim is NOT "we may solve an open problem" — it is that the
  instrument produces a specific genre of insight there
  (kernel-checked obstruction maps, class-maximal no-go theorems,
  minimal-input doors with proven implications, cheap refutations of
  plausible routes), and sprint 2 tests whether that genre holds up
  on harder territory than sprint 1's.

**Honesty clauses.** (1) No Track-B item is framed as "attempt to
prove <open problem>"; each is framed as a deliverable that is
valuable under BOTH outcomes. (2) A Track-A failure is reported as
the node map of exactly where it died — which is itself the
depth-limit measurement. (3) The pre-declared sprint-1 disciplines
carry over wholesale: METHODS.md in full incl. Part III, R1–R4,
recon-before-freeze, adversarial gates before every executor wave,
the ceremony per landing, statement changes house/human-only,
stop-and-flag with the ≥2× re-cut rule, the 4-agent throttle, the
incremental-write mandate, no `.All` imports in executor files.
(4) Assembly debts may be scheduled past the sprint and reported as
such. (5) The catch ledger continues; catches against the HOUSE's
own designs are reported with particular prominence (the sprint-1
precedent: the Q6b main-term catch).

**Context at registration** (to be finalized at signing): sprint 1
complete — the six questions closed (Q2 the least-k atlas with M₄ < 2
unconditional; Q3 the interface extraction; Q4 the windowed-BV
statement; Q5 the constrained no-go + the razor-boundary pair; Q6a
the parity wall; Q6b the door + the wall∧door dichotomy); Chen-2
[landed / flagged at <node>]; the corpus at ~[N] kernel-checked
declarations, 3 standard axioms throughout; [M] catches, 0 wrong
proofs.

---

## TRACK A — the depth probe: effective N(T) / local zero-density

**The registered question (A1).** Land, kernel-checked and
axiom-clean, an effective local zero-density estimate for ζ:

> `#{ρ : ζ(ρ) = 0, 0 < Re ρ < 1, |Im ρ − t| ≤ 1} ≤ C·log(|t| + 2)`

(the Riemann–von Mangoldt local form), together with the harmonic
zero-sum bound it exists to feed (the O(log T · log log T) form of
Σ 1/|t − γ| over nearby zeros, or the precise variant the design
freeze fixes). *Known:* classical, textbook (Titchmarsh ch. 9;
Davenport ch. 15–16); absent from mathlib AND the corpus (verified,
Rb-4 recon). *Unknown (the registered quantities):* (i) whether the
argument-principle machinery (the rectangle contour count against
ζ's logarithmic derivative, the Backlund-style bounds) decomposes
into gated C-nodes the way the SW contour arc did, or hides a
D-tier intermediate the recon layers have not seen; (ii) the cost,
against the SW arc's as the baseline — the METHOD-COMPOUNDING
measurement (the SW arc was built before Part III, the gate
discipline, and the witness ladder existed in their current form).

**The registered consequences (A2, in dependency order, each its own
outcome line).**
- **A2a — N1**: `|ζ(σ + it)| ≤ C·log(|t|+2)` near σ = 1 (Titchmarsh
  3.5-grade; the Rb-4-identified reusable C-node; the dTerm/zeta_shift
  scaffolding exists).
- **A2b — the one-power segment bound**: `|ζ'/ζ| ≤ C·log T` on the
  zero-free segment near σ = 1 (needs A1; the landed two-power box
  bound is the thing being beaten).
- **A2c — MmuRate discharges**: the effective Möbius rate from the
  landed ψ-PNT via the Perron/1/ζ route (the Q6a-4/Rb-4 route map,
  nodes Rb-1..7, with Rb-4 = A1+A2b); **THE TROPHY: the parity wall
  goes unconditional** (parity_wall_effective's MmuRate hypothesis
  discharges; the Q6a debt closes).
- **A2d (stretch)**: `Mlambda_rate` unconditional ⟹ the
  LambdaSummatory chain closes end-to-end.

*Resolved =* A1 + A2c land (the wall unconditional). *Partial =* any
prefix (A2a alone is already a corpus asset). *Informative failure =*
the node map of where it died, with the D-tier intermediate named
(the Rb-4 pattern, one level deeper).

**Track A protocol.** Opens with a design freeze (house) off the
Rb-4 report + a fresh scoping recon of the argument-principle
decomposition; adversarial gate; then waves. Budget ~1.5 days under
the throttle; the mid-sprint checkpoint (below) can extend or cut it.

## TRACK B — the frontier probe: insight-shaped deliverables

**B1 — the weight no-go atlas (the flagship bet).** Registered
question: extend the two landed atoms (`heavy_semiprime_obstruction`:
the E2-above-y mass is invisible to every decoration of the landed
weight; `deficit_floor_of_certs`: the razor cannot fund its own
P₁-deficit) to the CLASS-MAXIMAL delimitation: *no weight readable
from the landed decoration data (the ω-counts, the square-strip, the
triple indicator — arbitrary real coefficients, arbitrary finite
combinations) certifies P₁ from the landed carrier bounds.* *Known:*
the two atoms, kernel-checked. *Unknown:* whether the atoms extend to
the full decoration-readable class, and the exact class boundary (the
switch-side analogue of the M_k atlas). *Resolved =* the class-maximal
theorem with an exact boundary; *informative failure =* the widest
class the atoms DO close, plus the named escape (a decoration the
argument cannot see past — itself a finding about where twin-progress
must come from).

**B2 — the TwinB_min attack-surface map.** Registered question: run
the Q6a-4 recon pattern (route census → per-route refutation-or-
survival, at proof level against the landed corpus) on the classical
routes toward the P₁ lower sieve — at minimum: (i) Chen's reversal
(the switch pointed at P₁), (ii) weighted upper-lower sieve
combinations (Harman-style alternation), (iii) the vector/dispersion
route (the level-beyond-1/2 inputs feeding a lower form). Each route
terminates in either CORPUS-REACHABLE PARTIAL PROGRESS (a statable
node map) or a NAMED MISSING THEOREM (the Rb-4 outcome genre).
*Resolved =* ≥ 3 routes mapped to terminal precision; *jackpot
(not promised) =* one route survives recon deep enough to yield a
statable partial-progress node. The R4 tripwire is ARMED at maximal
sensitivity: any route seeming to reach P₁ from landed material is a
definitional alarm, not a result.

**B3 — the GEH_min door.** Registered question: state the minimal
equidistribution input for H₁ ≤ 6 through the corpus's variational
stack (the Q6b door pattern at the Q3-scoped target), with the
implication skeleton `GEH_min ⟹ H₁ ≤ 6` proven modulo the named
analytic inputs (the k=5-hardwired moment layer parametrized, not
rebuilt). *Known:* GEH ⟹ H₁ ≤ 6 classically; the Q3 recon's scope
map (the full route is multi-quarter — NOT attempted). *Unknown:*
the minimal interface's exact shape and whether the implication
skeleton is executor-tractable at the Q6b-DOOR grade. *Resolved =*
the door file lands (the Prop + the skeleton + anti-vacuity);
*informative failure =* the precise point where the k=5 hardwiring
resists parametrization.

**B4 — the log-Chowla distance map (recon only, no proof work).**
Registered question: what would formalizing Tao's logarithmically-
averaged two-point Chowla (the nearest actual THEOREM to the twin
frontier) cost from this corpus? Deliverable: the dependency map
(entropy decrement / the Elliott reduction / the multiplicative-
function machinery), classed per node against mathlib's and the
corpus's current state, with a total estimate. *This is a
measurement, not an attempt* — the first cost map of the distance
between a formalization corpus and the modern analytic frontier.

## Structure

- **Two tracks in parallel under the 4-agent throttle**, nominal
  budgets: Track A ~1.5 days, Track B ~1.5 days (B1 the largest
  share; B4 ≤ 200k total).
- **THE MID-SPRINT CHECKPOINT (registered, ~day 1.5): JYH rebalances
  between tracks** on the evidence — extend A at B's expense, or
  vice versa; the checkpoint decision and its rationale are recorded
  in the ledger (the sprint-1 Q1-checkpoint pattern).
- **THE EMERGENT-LEAD SLOT (registered).** Sprint 1's best outputs
  (the wall∧door dichotomy, the self-funding no-go) were unregistered
  emergents. If execution surfaces a lead judged stronger than a
  registered item, the house MAY reallocate to it via a transparent
  amendment (the A1/A2 pattern: appended, never editing the frozen
  text, JYH-ratified) — at most ONE such reallocation per track.
- **Registered exclusions** (the avoid-list, binding): no
  unfinishable monuments (ternary Goldbach, full log-Chowla
  formalization); no "attempt to prove <open X>" framings; no
  explicit-constant optimization grinds.
- **Reporting**: the sprint-2 chapter reports per-track outcome
  tables with costs, the catch-ledger delta, the reuse coefficients
  against sprint-1 baselines, and the method-compounding measurement
  (A's cost vs the SW arc). Nothing omitted for being unflattering.

## The success criteria, stated before the fact

Sprint 2 SUCCEEDS as an experiment regardless of how many items
resolve, if and only if every item terminates in one of its
registered outcome classes with costs reported. The INTERESTING
result — the one the writeup needs — is the shape of the frontier:
where the method's cost curve bends (Track A) and what the
insight-genre yields where proof is impossible (Track B). A sprint
where A dies at a named intermediate and B produces three obstruction
maps is a SUCCESSFUL experiment; a sprint reported as "we solved
everything" would mean the questions were badly chosen.

*Ratification trail: the two-track direction + avoid-list + checkpoint
+ emergent-slot structure, JYH 2026-07-15 ("yes, this sounds good").
The registration signature = the commit ratifying THIS text after
sprint-1 close, recorded here at signing.*
