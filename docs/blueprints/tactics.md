# Tactic engineering ledger (standing doc)

*Fable, 2026-07-11. Ratified direction from the user: tactic development is
a first-class planning axis — "make the work shorter and the proofs more
concise by writing tactics suited to the proof exploration." Process rule:
every rung BLUEPRINT includes a tactic-opportunities pass against this
ledger, and every rung CLOSE-OUT appends new friction observations. Tactics
are project code (`Salt/Tactic/`), promotable to mathlib when mature.*

## Doctrine

- A tactic node is justified when a friction pattern has appeared in ≥3
  executor reports, or when it unblocks an otherwise-infeasible node (the
  reflection case). Evidence column below cites actual nodes.
- Tactic code follows the same rules as proof code: kernel is the referee,
  no `native_decide` anywhere in a proof path (compiled evaluation is fine
  *inside tactic search*, but the produced proof must check pure).
- Classes: tactic nodes get the same A–D grades; metaprogram nodes are
  Opus-tier by default (the `TacticM` API is unforgiving).
- **Incompleteness doctrine (user, 2026-07-11):** tools capture real IDEAS
  and minimize mechanical cruft; no toolbox is complete and none should
  try to be. Corollaries: (i) incomplete tools must FAIL CLEANLY, leaving
  honest, readable residual goals (a documented contract — the
  `eventually_budget` model), never a half-transformed goal; (ii) do not
  chase the completeness asymptote (the growing-simp-set monster) — stop
  at the idea boundary; ten crisp tools beat one oracle; (iii) tactic
  incompleteness is SAFE by construction: tactics are search, the kernel
  checks — a bad tactic wastes time, never soundness. Readability is a
  first-class goal: idea-level tactics make the proof text mirror the
  informal sketch.

## The candidates (evidence-ranked)

### T1 — `CertEval`: reflection evaluator for rational certificates — class C, HIGH leverage
**The k=105 unblocke.** A verified evaluator for the certificate kernels
(`biQuad`/`biQuadW`, `DInt`, `simplexInt`/`ofPoly` closed forms) over
binary-representation `ℚ`, plus one soundness theorem; certificate checks
become single kernel computations instead of generic `norm_num` grinds.
**Evidence:** `J_Fstar_0..4` needed `maxHeartbeats 10000000` EACH for a
56-coefficient polynomial (3,136-term sums, `Certificate.lean:179-249`);
a single `m` timed out at 200k heartbeats. The k=105 certificate
(~10⁴–10⁵ terms) is INFEASIBLE on the generic path and plausibly a
weekend with reflection. **When:** before the k=105 certificate rung;
independent of BV — can be probed any time. **Probe:** re-verify
`J_Fstar_0` via a toy reflective evaluator; target ≥100× heartbeat
reduction.

### T2 — `eventually_budget`: the ∀ᶠ threshold-stack assembler — class C, HIGH leverage
Combine a list of eventual facts (`∀ᶠ N, fᵢ N ≤ εᵢ`) against a monotone
budget goal (`∀ᶠ N, Σᵢ fᵢ N < margin`), automating the `max`-threshold
plumbing and the per-piece `≤ U/K` splits.
**Evidence:** `WinFrontierDischarge` (the W5-7 threshold assembly),
`GapsUncond` ("7 vanishing pieces, each ≤ U/700000" + a private helper
family `eventually_logN_ge/eventually_logR_ge/eventually_div_logR_le/
eventually_polylog_ratio_le/eventually_poly_o_linear/eventually_R_ge/
eventually_DL` — ~120 lines of pure plumbing), `windowPNT_of_piAsymp`
(threshold extraction). Recurs in EVERY analytic assembly; V3/V5 of the
BV rung will hit it again. **When:** early in the BV rung (V3 is the
natural first consumer).
**STATUS: LANDED at both layers** (`Salt/Tactic/EventuallyBudget.lean`:
the Finset combinators + Tendsto extractors (mathlib duplicates aliased,
not re-proved) + the `eventually_budget [h₁,…]` macro with `</≤` handling;
kernel-checked self-tests + `#audit_axioms` dogfood. Known edge: the macro
needs syntactic piece-match — documented).

### T3 — `budget_num`: explicit-constant arithmetic closer — class B
A `norm_num`/`nlinarith` wrapper pre-loaded with the standard analytic
numerals (`Real.pi_lt_d2`, `log 4 + 4 ≤ 5.39`-style, `(log x)² ≤ 4x`,
`1 + log Q ≤ 2.45 log x` shapes) and product-hint heuristics.
**Evidence:** the `nlinarith` product hints in `AnalyticLS` ("needed
explicit `(N²·P)·(10−π²) ≥ 0`"), `BDH`'s numeral chain (≈5792 ≤ 6000),
`win_ratio_core` cert arithmetic, the `13N`/`4πN` slack discharges.
**When:** opportunistic; a shared lemma file (`Salt/Tactic/Numerals.lean`)
is step one and is class A.

### T4 — `salt_cast`: cast-discipline macro + conventions — class A/B
`push_cast`-led macro plus a curated `@[simp]`-cast set for the recurring
ℕ-division/floor/`% q` shapes.
**Evidence:** cast friction reported by nearly every executor: `Farey`
(the whole difficulty was "ℕ/ℤ/ℝ cast friction"), `PhiSum`
(`((Q/d : ℕ):ℝ)` vs real division), `TypeSums` (the `((a*b:ℝ):ℂ)`
ascription trap), `JcalPos`, the seam's `⌊(64N:ℝ)⌋₊` plumbing. **When:**
now-ish; cheap, immediate payoff.

### T5 — `#audit_axioms` command — class B
An in-file command `#audit_axioms decl₁ decl₂ …` that FAILS elaboration
if any declaration depends on axioms outside
`{propext, Classical.choice, Quot.sound}` — turning the scratch-file
protocol into a committed, CI-checked assertion at the bottom of each
track's `All.lean`.
**Evidence:** every single node verification this session ran the manual
scratch `#print axioms` dance (~40 times); the lint's phase-3 now does it
out-of-band, but in-file is stronger (fails at build time, not lint
time). **When:** any idle slot; pairs with wiring into `lean_action_ci`.
**STATUS: LANDED** (`Salt/Tactic/AuditAxioms.lean`, `#guard_msgs`-pinned
self-tests incl. a negative on `Lean.ofReduceBool`; adopted in
`Salt/BV/All.lean` — remaining tracks' `All.lean` adoption queued for the
next close-out sweep).

### T6 — Finset-reindexing helper library (+ aesop set) — class B, library-not-tactic
The `sum_nbij'`/`sum_sigma`/`sum_comm'`/fiberwise patterns, packaged.
**Evidence:** `ArithmeticLS`'s `sum_expSum_sq_le_of_spaced` engine,
`TypeSums`' `reindex_core`, `BDH`'s `regroup`, `PhiSum`'s divisor swap —
four independent reimplementations of adjacent idioms this session.
**When:** harvest AFTER BV (which will add 2–3 more instances to
generalize from); premature abstraction is the risk.

### T7 — instance-hygiene guard — class B, investigate-first
The `DecidableEq (DirichletCharacter ℂ q)`/`Fintype` clash cost the BDH
node its only real snag (resolved by a scoped priority-5000 Classical
instance + `Subsingleton.elim`). Candidate: a project-wide scoped
instances file + a linter that flags decidability-instance mismatches
across module boundaries. **Evidence:** `BDH.lean` friction report; the
`open Classical in`-before-docstring trap in `CharLS`. **When:** if it
bites a third time.

### T8 — `slack_report`: retrospective proof-tightening miner — class C/D, SPECULATIVE (research-note)
User-raised question (2026-07-11): can landed proofs be tightened
retrospectively as new results arrive? Two mechanizable halves:
(1) **budget re-runner** — the explicit-constant doctrine makes every
estimate chain re-computable; when a sharper input lands (e.g. a
Mertens-sharp `κ⁻¹ ≲ log D` vs the landed `5√D`), re-run downstream
budgets and report every numeral that improves (concrete first target:
`GapsUncond`'s `Dfin ~ 10²⁸·A²` would drop to `~10¹⁷`-scale);
(2) **application-site slack analyzer** — a metaprogram walking proof
terms, comparing each lemma application's strength to what the step
consumes; would have found the struck-max artifact (6th correction)
retrospectively. Framing: computable reverse mathematics — "weakest
sufficient interface" as a batch query (done manually for WindowPNT →
PiAsymp). **When:** genuinely speculative; revisit when a sharpened
input actually lands (the Mertens case) or at a rung close-out with
idle capacity. Evidence will accumulate passively via the named-gate
discharges.

### Doctrine addition (2026-07-11, evidence-based): kernel lemmas land PUBLIC
~270 lines of duplication in one wave (V2.Perron replicated 6 PV privates,
LS-bil replicated the harmonic kernel again) traced to mathlib-style
`private` habits on shared analytic kernels. New rule for Salt executors:
chord/geometric/harmonic/`dist₁`-kernel lemmas land PUBLIC by default
(namespaced; `private` only for genuinely proof-local scaffolding).
Retroactive de-privating of `PolyaVinogradov.lean`'s six kernel lemmas +
dropping the two replica blocks = a queued close-out sweep item.

## The schema criterion (user doctrine, 2026-07-11)

**When a pattern of reasoning becomes visible in a domain and CANNOT be
captured in a lemma — because the recurring object is a proof SHAPE with
holes (a motive pattern), not a proposition — that is the signal to
capture it as a tactic or tactic-group** ("perform induction with this
hypothesis shape"; "handle the base shape of this class"; "handle the
step like this"). Capture ladder, cheapest first:
(a) **custom induction/elimination principle** — a higher-order LEMMA with
a motive; `induction … using it` gives most of the tactic experience with
zero metaprogramming; (b) **macro** bundling the eliminator + standard
discharge moves; (c) **elab tactic** only when genuine syntactic goal
analysis is required.

### T9 — schema harvest candidates (evidence-ranked, post-BV)
- **`dyadicRec` / dyadic-assembly** (4+ occurrences: `interval_decomp`
  strict-length induction, BDH conductor fibering, TypeII d-blocks,
  V2b-close's geometric sums): "split dyadically; per-block obligation;
  geometric close dominated at top/bottom." Start at ladder rung (a) —
  an eliminator parameterized by the block motive + domination direction.
  Merges with T6's library harvest.
- **`regime_split`** (the `√(a+b) ≤ √a+√b` four-regime budget expansion —
  AnalyticLS, BDH, V2b): rung (b) macro over the split + per-regime goals.
- **`guard_collapse`** (vanishing-factor filter elimination — typeIIData/V,
  MulChar off-units, lamPhiContractM off-box; three tracks): rung (a)/(b).
- **constants-first linter** (the ∃-opacity discipline as a CHECK: flag
  proofs introducing the modulus before obtaining ∃-constants): rung (c),
  speculative — pairs with T8.
Harvest AFTER the BV rung closes (V2b-close + V3.1 will add instances to
generalize from; premature abstraction remains the risk).

## Period-planning hooks

- **Blueprint checklist line:** "Which ledger tactics would shorten this
  rung's dominant node class? Any new tactic node justified?"
- **Close-out checklist line:** "Append new friction patterns + node
  citations to `tactics.md`."
- Current standing plan: T4+T5 opportunistic (any idle wave slot);
  T2 early in the BV rung; T1 gates the k=105 certificate rung and can be
  probed in parallel anytime; T3 step-one lemma file cheap; T6/T7 wait
  for more evidence.
