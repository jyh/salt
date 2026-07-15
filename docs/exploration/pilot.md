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
- 2026-07-14 evening: **P-A + P-B COMPLETE (Salt/TwinBar/Enlarged.lean,
  361 lines, kernel-checked, first attempt).** The mathematics:
  `twin_bar_enlarged` (M₂^{[δ]} ≤ 2(1+δ)·log 2 for ALL continuous F on
  the enlarged simplex — finiteness YES, via a change-of-variables
  pull-back onto the landed twin_bar, NOT a re-derivation) and
  **`no_twin_weight_enlarged`: the k = 2 no-go PERSISTS under
  ε-enlargement for δ < δ₀ = 1/log 2 − 1 ≈ 0.4427** (concrete admissible
  δ = 2/5 pinned) — to our knowledge unrecorded at k = 2. Hygiene:
  `twin_bar_asymmetric`/`twin_bar_signed` citable; the density-bridge
  question stated as a Prop.
- **Pilot lesson #2 (the process validation — worth more than the
  theorem):** the executor found that the naive witness F ≡ 1 on the
  unconstrained enlarged carriers gives ratio > 2 near δ = 1 — which
  would "prove twin primes under EH" and is therefore a definitional
  alarm, not a result. It identified the honest functional (Polymath8b's
  ε-trick constrains the MARGINALS to the original simplex, making the
  would-be witness inadmissible), proved the a-fortiori-valid upper
  bound, and ESCALATED the interpretation question instead of landing a
  false exhibit. The naive-executor failure mode the pilot existed to
  surface — surfaced and handled.
- **FABLE ADJUDICATION of OPEN 1**: per Polymath8b's ε-trick the gate
  stays 2 (the enlargement is paid by the marginal constraint and the
  GEH-level requirements, not by rescaling the gate), so
  no_twin_weight_enlarged delimits the honest constrained problem for
  δ < δ₀. Above δ₀: genuinely open at k = 2 (circumstantial evidence —
  Polymath8b used k = 3, not k = 2, for gaps ≤ 6 under GEH — suggests
  the constrained sup stays < 2, unproven). Drafting-time TODO: verify
  the k = 2 enlarged threshold really is unrecorded (literature sweep).
- **Extracted protocol rules for the sprint (from the experience
  report):** (R1) recon precedes question freezing — including the
  TARGET'S exact variational/functional definition, not just the Lean
  surface; (R2) a T3 executor first asks "can this perturbation be
  pulled back onto a landed theorem?" before porting machinery; (R3)
  an explicit early checkpoint "is the carrier/functional definition
  unambiguous?" — if not, escalate within the first attempt; (R4) a
  would-be witness that implies something OPEN is a definitional alarm.
  Budget calibration: P-A cost ≈ 1 web check + ~5 build cycles + one
  de-risking scratch; T3 sprint budgets sized to this.
- P-C DISPATCHED (the k = 3 probe, P-A's lessons injected).
- 2026-07-14 night: **P-C COMPLETE (Salt/TwinBar/ThreeBar.lean, 466
  lines, first attempt).** THE FIND: the k = 2 magic identity is the
  β = 1/(k−1) CS-base tuning — normalization log((β+1)/β), weight-sum
  constant iff β = 1/(k−1), giving c_k = (k/(k−1))·log k = Polymath8b's
  bound RE-DERIVED FROM OUR OWN ATOMS. At k = 3: base = (slice)/2,
  normalization log 3, w-sum ≡ 3/2, **c₃ = (3/2)·log 3 ≈ 1.648 < 2** —
  the SHARP constant (route (b) pull-back onto twin_bar was assessed
  and REJECTED: it reaches only 3·log 2 ≈ 2.079; the sharp value needs
  the retuned base — the contrast with P-A's cheap pull-back is itself
  calibration data). Landed kernel-checked: the full analytic heart
  (logWeight_half, log_slice_CS general-β, w_sum_three, the three
  sliceCS, (3/2)log3 < 2, carriers) + `TripleBar` (the citable target)
  + **`no_triple_weight_of_tripleBar`** (the k=3 no-go MODULO the
  assembly — the gap exposed as exactly one lemma). DEFERRED with a
  precise OPEN note: the 3-D Fubini assembly (~300–500-line
  measure-theory port; mathlib has no turnkey simplex iterated-integral
  lemma) = node **TB3-ASM**, a sprint work item under Q2 (lands
  M₃ < 2 unconditionally — the atlas's second delimitation).
- **Pilot calibration datum #2 (P-C):** T3 probes split into a CHEAP
  find-the-sharp-constant phase (~6 build cycles, one sanity script —
  the discovery + the analytic core) and an EXPENSIVE formal-assembly
  phase (a rung of its own). Budget them separately in the sprint.
  The β-tuning pattern generalizes the whole M_k atlas cheaply at the
  pre-integration level — the reusable win.
- **PILOT MATHEMATICS PHASE COMPLETE** (one evening vs the 3-day
  timebox): P-A theorem + threshold δ₀; P-B hygiene + the bridge Prop;
  P-C sharp constant + conditional no-go + TB3-ASM scoped. Remaining
  pilot closeout (house session): the synthesized experience report,
  the sprint T3 budget table, Q5's refined phrasing (draft: "does the
  marginal-CONSTRAINED enlarged M₂^{[δ]} reach 2 for δ ∈ (δ₀, 1]?" —
  the sharpest boundary the pilot exposed — plus the Chen H-package
  perturbation leg), all at the pre-registration session with JYH.

## THE SPRINT IS LIVE (2026-07-15)

Pre-registered at commit `7ddeb491665ac2cc82055f0552f467587ee1c494`
(docs/exploration/preregistration.md). Wave 1 dispatched (all Opus):
- **Q1-recon** — the Chen-2 reuse audit (the twin-shape surface, the
  N-uniformity question, the W-trick at N, the VERBATIM/PARAMETRIC/
  MIRROR/RE-DERIVE census).
- **Q5a-probe** — the marginal-constrained enlarged M₂
  (Salt/TwinBar/Constrained.lean; the constraint store opens the
  docstring per Part III; routes: the support-edge slice split /
  the β-tuned base; R4 tripwire armed).
- **Q6a-recon** — the λ/Selberg-witness gap inventory (the
  consumed-field list of BoundingSieve, the exact-vs-ε agreement
  shapes, the Σλ = o(x) cost routes).
Held for wave 2: Q2 (TB3-ASM + the k=4,5 atlas), Q3 (GEH_min), Q4
(the windowed-BV literature sweep), Q5b (the class-freeze design
pass). Cost tracking per the registration: tokens + cycles +
decisions per question.

- 2026-07-15 ~09:00: **Q1-recon COMPLETE** (read-only; cost ≈ 102k
  tokens / 30 tool uses / ~7 min). THE STRUCTURAL REUSE DATA: corpus
  denominator ≈ 125k lines; **~63% VERBATIM** (the shift-blind
  backbone: LS/BV/SW/Tactic + CbarCert + SuperPanels + the Rosser/
  β-tuning/mass-ledger machinery — the dispersion BV's
  sup-over-residues form covers the Goldbach classes verbatim, the
  corpus's biggest luck); **~35% PARAMETRIC/MIRROR** (the carriers
  and operating point under the mechanical substitution n+2 ↦ N−n,
  d−2 ↦ N mod d, odd ↦ coprime-to-N); **~1–2% RE-DERIVE** — three
  localized items: (i) the N-dependent density ν_N(p) = 0 at p ∣ N +
  the ∏(p−1)/(p−2) singular-series correction (the twin chain's
  one-forbidden-prime inequality 3 ≤ p becomes an N-dependent finite
  exclusion set — THE structural asymmetry); (ii) the N-aware residue
  witness (a = Q−1's free gcd collapse → a CRT selection avoiding
  N mod p, nonvacuous since p ≥ 3); (iii) the ∀-N outer quantifier +
  opQ ≤ log N uniformity. Q1's design pass (Fable) will freeze the
  Chen-2 blueprint from this audit; the registered reuse coefficient
  gets its measured value at execution.
