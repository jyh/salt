# The Boundary Map

**What separates the proven crack in the parity barrier from the
twin prime conjecture — stated by the kernel.**

*(M-BOUNDARY synthesis, 2026-07-20. Raw data: the MB-1 dependency
sweep; theorems: `Salt/Entropy/Chowla/BoundaryMap.lean`; ledger:
pilot.md. All classifications refer to the machine-checked
log-Chowla-2 spine `log_chowla_two_conditional` /
`log_chowla_two_of_door`.)*

## The question

Tao's log-Chowla-2 is the only parity-type statement ever proven.
Having machine-checked its entire skeleton, we can ask the corpus a
question no human reading can answer reliably: **which special
properties of the Liouville setup does the proof actually consume,
where, and how many times?** Every consumption site is a place a
twin-prime transport must either preserve or replace.

## The map

Across the 37 keystone files of the spine, classified by actual
proof-term consumption (not mention):

**The logarithm enters at exactly two load-bearing sites.**
1. *Dilation covariance* — `w(qn) = w(n)/q`, the change of
   variables of Tao's Lemma 2.5 (carried by `dilation_error_div`,
   consumed by the Prop 2.6 engine).
2. *The normalizer value* — `Z ≈ log ω`, which converts the failure
   margin `ε·log ω` into `ε`.

A third apparent site (the normalizer positivity floor) is
weight-generic. **Everything else — including the entire sieve
side built this window (~21 files) — survives arbitrary
probability weights.**

**Complete multiplicativity enters at exactly one mechanism** —
the collapse identity `f(pN)·f(pN+p) = f(N)·f(N+1)` — and the
sign of λ is **inert**: the spine consumes only `λ(p)² = 1`;
`λ(p) = −1` has zero proof-term uses.

**The ±1 alphabet enters as the entropy fuel** — the `H·log 2`
ceiling that the decrement chain spends against the divergent drop
sum — and as hypothesis-generic boxing elsewhere.

## The theorems

1. **The log is forced** (`dilation_forces_log`): a weight
   satisfying the dilation covariance is the harmonic weight, up to
   scale. Logarithmic averaging is not a convenience of Tao's
   proof; it is the unique weighting compatible with the
   multiplicative change of variables at the argument's heart.
   Sharpness (`approx_covariance_not_unique`): the approximate
   covariance admits bounded multiplicative oscillation — the
   exact form is the honest rigidity.

2. **The multiplicative mechanism is exactly the real CM±1 class**
   (`collapse_iff_completelyMult`): for normalized ±1 functions,
   the collapse identity and complete multiplicativity are the
   *same condition*. Discovered by a GF(2) rank computation that
   inverted the design's expectation (we hunted a counterexample
   and found a rigidity), then proven by ordinary induction — a
   single collapse relation at the predecessor suffices.

3. **The unification**: the collapse identity is itself a dilation
   invariance — of pair-correlations, at the sign level. The two
   "special structures" of the crack are one principle in two
   guises: **the crack runs on dilation invariance, twice** — once
   in the measure (forcing the log), once in the sign system
   (forcing the CM±1 class).

## What this says about the twin transport

The von Mangoldt weights that twin counting needs fail exactly two
of the map's requirements, and *only* those two:

1. **The bounded alphabet** (entropy fuel): Λ is unbounded and
   sparse; the `H·log 2` ceiling and the Fannes/box machinery fail
   constitutively.
2. **The pair-correlation dilation invariance**: by the rigidity
   theorem, any surrogate satisfying the collapse mechanism *is*
   completely multiplicative ±1 — and Λ is not. There is no
   half-multiplicative middle ground; the class is closed.

Everything else in the crack — the circle method, the large
spectrum bound, the sieve machinery, the transport/Fubini plumbing,
the entropy library itself — is weight-generic and transports
freely.

**The door-minting conclusion:** a "transport door" (a minimal
hypothesis making the entropy argument reach twin-relevant
weights) must supply replacements for precisely (1) an entropy
budget for an unbounded weight system and (2) a dilation-invariant
correlation structure outside the CM±1 class. It cannot weaken
either requirement within the present mechanism — the rigidity
theorem closes that route. This is the precise shape of the wall
between log-Chowla and twins, and simultaneously the precise
specification any future door must meet.

## Honest open items

- The transport door itself remains unminted: the map specifies
  what it must contain; constructing a believable candidate is
  research (the natural continuation of this experiment).
- The natural-averaging question is now localized: removing the
  log from log-Chowla-2 requires replacing the dilation-covariant
  weighting — `dilation_forces_log` says there is nothing else in
  its class. Any attack on natural Chowla must break the change of
  variables itself, not the bookkeeping around it.
- The characterization is at the normalized ±1 level; complex
  unit-modulus analogues (Elliott-type) are unexplored formally.

---

## Addendum — THE TRANSPORT DOOR CAMPAIGN OPENS (the Gold Window,
2026-07-20, JYH: "let's go for the gold")

**TD-0 (house): the candidate families + the sweep protocol.**
Three candidate genres for filling the two slots:
1. **The abstract Siegel-oracle** (the HB triangle): axiomatize
   what a Siegel zero provides — a real CM±1 character χ with
   L(1,χ) anomalously small, forcing λ/μ to pretend to be χ —
   restated as fillers for the two slots (the correlation
   structure via the χ-twist; the budget via the induced bias).
   HB-ENGINE would later INSTANTIATE this door.
2. **Bounded CM surrogates** (the classical route): λ·χ-family /
   pretentious approximants to twin-relevant weights — slot 2
   free (they ARE CM±1), the question is whether any carries
   twin information (the parity wall's classical refusal —
   candidate walls live here).
3. **W-tricked normalizations**: Green–Tao-style residue-class
   restriction taming Λ's alphabet — slot 1 partially free, slot
   2 the open question.

**The sweep protocol** (the unique instrument): each frozen
candidate is mechanically tested against the skeleton's named
consumption sites (the boundary map's dependency table): does it
fund Fannes/the box (slot 1)? does its correlation structure
support the collapse's role in Prop 2.6 (slot 2)? does the
decrement's budget arithmetic survive? Each test is an
elaboration-probe + a falsity-probe per the standing doctrine.
**TD-R1 dispatched**: the oracle candidate's design recon.

## TD-R1 verdict (adjudicated): THE ORTHOGONALITY FINDING

All three oracle candidates are WALLS (probe-verified, ProbeTD.lean):
1. **χ_ℝ-as-weight**: passes BOTH slots (bounded; chiRe_mul makes
   it exactly CM±1(,0) — the rigidity theorem CERTIFIES it) — and
   is twin-INERT. The sharpest form of the parity refusal: the
   crack's machinery ACCEPTS the Siegel character and goes
   nowhere. The wall is the LINKAGE, never the slots.
2. **Λ·(1−χ_ℝ)**: fails BOTH slots — the χ-twist tames neither
   Λ's alphabet nor its non-multiplicativity.
3. **The abstract two-slot form**: an impossibility triple —
   {bounded ∧ shift-2 pair-collapse ∧ twin-detecting} is mutually
   exclusive (slot 1 forces bounded; slot 2 + rigidity forces
   CM±1; the linkage forces Λ-detection).

**THE HEADLINE: the two only-ever-proven parity mechanisms are
STRUCTURALLY ORTHOGONAL.** The Siegel oracle supplies a
FIRST-MOMENT object (psi1Chi ≈ −residue, a mean + a density bias
— sieve-consumable, exactly R3c/HB-ENGINE's food) while the
entropy spine's slot 2 consumes a PAIR-COLLAPSE object. Category
mismatch; they cannot compose. Bonus observation: the oracle's
forced correlation is dilation-covariant at exponent β₁+1 — a
measure-shaped covariance, pointing at an Elliott-type
first-moment spine as its natural (non-existent) consumer.

**Next nodes (dispatched):** TD-R2b — freeze the ORTHOGONALITY
WALL as a Lean impossibility (peer of the parity-wall family;
materials all landed). TD-R2a — the ELLIOTT REDESIGN recon: can
the entropy architecture be rebuilt to consume first-moment
slot-2 content? If yes, the oracle's dilation-covariant first
moment becomes a genuine filler — the wall converts to a
redesigned-door target. HB-ENGINE confirmed as the oracle's
correct (sieve) home; the two doors stay orthogonal.

## The orthogonality wall, frozen (TD-R2b — kernel-proved)

`Salt/Entropy/Chowla/TransportWall.lean` proves the impossibility
triple is real: `PmNormalized` (the ±1 slot-1 form) +
`PairCollapse` (shift-1 slot 2) drop any weight into the CM±1
class via the rigidity engine (`slots_iff_completelyMult`), and
that class contains twin-blind members — `w ≡ 1` passes both
slots with constant pair-correlation (`const_satisfies_slots` +
`const_twin_blind`). Hence **`orthogonality_wall`** (the slots
cannot force even minimal twin detection) and the meta-form
**`no_slot_derived_twin_linkage`** (NO linkage predicate can be
both slot-derivable and detection-sufficient). Honest scope: this
refutes slot-satisfaction alone; the strong wall (no CM±1 weight
controls the twin carrier through the spine) is the Chowla-family
open problem, prose-only.

**The satisfier class, mapped exactly (wall-L1, 2026-08-15).**
`Salt/Entropy/Chowla/PinDichotomy.lean` completes the picture the
wall leaves open: inside the slot class twin-blindness is a single
point. `blind_iff_const` — for `PmNormalized` + `PairCollapse`
weights, failing twin detection is EQUIVALENT to `w n = 1` at
every `n ≥ 1` (the pair correlation is globally constant, the
seeds `n ∈ {1,2,4}` pin the constant to `+1`, and the step
`k ↦ k+2` carries `+1` over every index; the route's sufficiency
has its own `GF(2)` control at `scripts/l1_gf2_control.py`).
Contrapositive: `pin_iff_detecting` (with `pinned_door` /
`pin_minimal`) makes ONE pinned sign `w n = -1`, `n ≥ 1`, exactly
detection — the computed bottom element of the
detection-sufficient hypotheses above the slots, dual to
`no_slot_derived_twin_linkage`; `liouville_pinned` inhabits the
detecting side at the separator `(3,7)`. The statements use a
GUARDED notion `TwinDetecting'` (`TwinDetecting` plus `1 ≤ n`),
landed BESIDE the frozen definition, never replacing it: the
n = 0 slack in the landed definition is real, and
`slack_witness_twinDetecting` freezes the witness — `5` at `0`,
`1` elsewhere — which passes both slots and satisfies
`TwinDetecting` at `(m,n) = (3,0)` while detecting nothing.
Because `twinDetecting'_imp` runs `TwinDetecting' ⟹
TwinDetecting`, the UNGUARDED definition is what makes
`orthogonality_wall` and `no_slot_derived_twin_linkage` the
stronger theorems, so `TransportWall.lean` stays byte-frozen; the
kernel holds the fence (`blind_iff_const_fails_unguarded` shows
the dichotomy is FALSE at the unguarded definition, and any
in-place re-guarding would make the slack witness unprovable and
break the build). Scope unchanged: boundary-map completion, no
claim about twins.

**The door criterion, and which slot does the collapsing (wall-L5,
2026-08-15).** Two readings of the wall-L1 point, both in
`PinDichotomy.lean`.

*Upward — the criterion.* `door_criterion` adjudicates a whole
genre of proposals at once. For any family `P` of weights that
STRENGTHENS the two slots (`hP : P w → PmNormalized w ∧
PairCollapse w`) and is insensitive to the value at index `0`
(`hP0`, the insensitivity the slots themselves have, since neither
reads that index), `P` contains a twin-blind member exactly when
`P` contains the constant weight `1`. `door_criterion_exists` is
the hypothesis-lighter form, with "contains a weight that is
constantly `1` on `n ≥ 1`" on the right. Testing a proposed
slot-strengthening for blindness is thereby a question about one
explicit weight rather than a search over the family.
`hP0` is necessary, and the kernel says so:
`door_criterion_needs_zero_blindness` proves the `hP0`-free
statement FALSE, off `P := (· = slackWitness)`. So the precise
wall-L1 statement is that the blind set is a single point IN THE
VALUES AT `n ≥ 1`; the value at `0` is unconstrained by both
slots, and `slackWitness` inhabits that fibre.

*Outward — degenerate blindness.* Drop slot 1's `±1` alphabet and
admit the value `0`, and the picture inverts. `corr_zero_blind`:
every weight whose pair correlation `n ↦ w(n)·w(n+2)` vanishes
identically fails the detection clause — that is, every weight
whose support contains no pair `{n, n+2}`, an uncountable family,
all of it blind, with `delta1w` (the point mass at `1`) the
kernel-borne instance via `delta1w_corr` / `delta1w_blind`.
Detectors live there too: `chi4w_detecting'` separates the twin
pair `(3,5)` from the non-twin pair `(2,4)`, since
`χ₄(3)·χ₄(5) = -1` while `χ₄(2)·χ₄(4) = 0`. Both weights satisfy
slot 2 (`delta1w_pairCollapse`, `chi4w_pairCollapse`) and fail
slot 1 (`delta1w_not_pmNormalized`). So slot 2 alone carries a
detector and an uncountable blind family side by side, and slot
1's `±1`-normalization is exactly what collapses that family to
wall-L1's single point.

*The reach, stated.* `hP` reaches only families strengthening the
frozen sharp slots; the probe's literal candidate-3 slot 1 (the
windowed first-moment budget, `TransportWall.lean:14-17`, which
"does not grade `w` to `±1`") does not imply `PmNormalized`, so
the criterion does not adjudicate candidate 3 as literally posed.

## TD-R2a verdict (adjudicated): REDESIGN-VACUOUS — and THE
## POLARITY FINDING

The Elliott first-moment-spine redesign is determinately
impossible, on four independent lines:
1. **The information gap**: a first-moment (1-point) spine carries
   zero twin content; twins force a ≥2-point object at extraction,
   and at that point slot 2 is back to pair-transport (CM±1,
   closed) — the orthogonality wall survives the redesign.
2. **The Halász coincidence** (exact, not loose): the first-moment
   analogue of the (2.11)→(3.15) entropy chain IS the classical
   Halász–Wirsing mean-value proof (1-point mutual-information
   decrement = pretentious distance). The entropy method's
   value-add is confined to ≥2-point order; the 1-point niche is
   classically occupied, twin-free.
3. **The category mismatch** (TD-R1, re-localized to the forced
   reintroduction point).
4. **THE POLARITY FINDING (new)**: the entropy method is an
   ANTI-BIAS / upper-bound instrument — it kills persistent
   correlations against the H·log2 budget and concludes
   `¬logChowla2Fails`. Twins need a LOWER bound; the oracle
   supplies a PRO-bias (the density twist). Opposite polarities:
   entropy removes signal, the oracle supplies it, twin-counting
   consumes it. This applies to ANY entropy redesign, not just
   the oracle one.

**Family-3 (W-trick) mini-sweep: not a door.** Mean-normalization
fixes neither unboundedness nor a newly-surfaced **sparsity
sub-wall**: slot 1's real requirement is *balanced* bounded (~log2
entropy per site); the prime indicator is bounded but sparse
(~loglog/log per site — the fuel tank empty regardless). The
W-trick aids exactly the machinery that is already weight-generic
(circle/sieve L² control). Slot-1 spec hereby strengthened:
"bounded alphabet" → "balanced bounded alphabet."

**THE CAMPAIGN CLOSES.** All three TD-0 families swept: family 1
(oracle) = the orthogonality wall, kernel-frozen; family 2
(bounded CM surrogates) = twin-inert by rigidity (χ_ℝ the sharp
exemplar; the strong wall = the Chowla-family open problem,
prose-only class D); family 3 (W-trick) = not a door. The
transport door remains unminted BY THEOREM along every surveyed
route; its specification is complete; every gram of oracle
content routes to the sieve — **HB-ENGINE is the constructive
continuation**. The boundary experiment's answer to "can the
crack transport?" is: not through these walls, and now the walls
are named, priced, and partly kernel-proved.
