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
