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
