# Exploration pilot — the M₂ boundary probe (T3 calibration)

Status: LIVE (started 2026-07-14 evening). Disclosed-and-excluded per the
pre-outline §7: this pilot calibrates budgets and stopping rules BEFORE
pre-registration; its outcomes do not count toward the pre-registered
stats. Timebox ~3 days. This file is the start of the exploration ledger.

## Pilot lesson #1 (before any probe ran)

The recon pass (PILOT-recon, 2026-07-14) found that two of the three posed
relaxations were ALREADY answered by the landed statement: `twin_bar`
(Salt/TwinBar/Impossibility.lean:173) hypothesizes ONLY
`ContinuousOn (uncurry F) R₂` — no symmetry, no sign condition (the proof
is deliberately sign-agnostic: the discriminant CS and the no-sign Tonelli
swap). The landed class was already maximally lax on those two axes.
**Protocol rule extracted: recon precedes question freezing** — adopted
for the sprint's pre-registration (questions are frozen only after a recon
pass on each).

## The probes

**P-A (the genuine unknown — the core probe): the δ-enlarged simplex at
k = 2.** Define the enlarged carriers (integration ranges extended to the
(1+δ)-simplex: R₂^δ = {t₁ + t₂ ≤ 1 + δ}, slices 0..(1+δ−t₂)). The landed
proof's two load-bearing mechanisms visibly deform:
- `logWeight`'s value log 2 came from the slice length and weight base
  being the SAME a = 1−t₂ (∫₀^a (a+t)⁻¹ = log 2, a-uniform). On the
  enlarged simplex the slice is a+δ and the uniformity breaks — the
  analogue is log((2a+δ')/a)-shaped, a-dependent, and DIVERGES at the
  corner a → 0 (t₂ → 1) where the enlarged slice keeps length δ.
- the magic identity w₁ + w₂ = 2 deforms to w₁ + w₂ = 2 + (correction).
Questions, in order: (i) does the w-machinery still give a FINITE upper
bound M₂^{[δ]} ≤ c(δ) for small δ > 0 (the corner may force a genuinely
different slicing or a δ-dependent weight)? (ii) if yes, for which δ is
c(δ) < 2 (the no-go persists — a new delimitation theorem strictly beyond
Polymath8b's recorded k=2 statements)? (iii) if the route fails at the
corner, characterize the failure precisely (an open note with the exact
obstruction is a full deliverable). Classical context: the ε-enlargement
is exactly Polymath8b's route to gaps ≤ 6 under GEH at k = 3; the k = 2
enlarged threshold is (to our knowledge) not in the literature.

**P-B (formal hygiene, cheap): state the already-implied delimitations
explicitly** — corollaries of `twin_bar` making the sign-freedom and
symmetry-freedom manifest in the statement names (the atlas wants them
citable), plus the density-bridge open note (the landed bound is per-F
continuous; Polymath8b's M₂ is an L²-sup — state the bridge question
precisely, do not attempt it).

**P-C (atlas feeder, medium — HELD until P-A's first report):** extend
the w-machinery to k = 3 (an M₃ upper bound with an explicit constant).
Feeds Q2. Dispatched only after P-A's experience report calibrates the
budget.

## Pilot deliverables (unchanged from §7)

(i) the T3 experience report — executor behavior on open-ended questions,
honest stopping rules, where human decision points landed; (ii) calibrated
T3 budgets for the sprint; (iii) the mathematics in whichever reportable
form (delimitation lemma / refutation / precise open note); (iv) Q5's
refined phrasing.

## Ledger

- 2026-07-14: PILOT-recon complete (the M₂ formal surface; lesson #1
  above). P-A dispatched (with P-B as warm-up in the same file domain).
  P-C held.
