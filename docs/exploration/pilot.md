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

- 2026-07-15 ~09:15: **Q6a-recon COMPLETE** (read-only; cost ≈ 95k
  tokens / 29 tool uses / ~9 min). THE HONEST-SHAPE FINDING (R1
  earning its keep — the registered phrasing was unsatisfiable):
  "agreeing in EVERY field" is impossible (weights is a real field;
  1+λ ≠ 1−λ pointwise) and exact-rem agreement is unmeetable (needs
  Σ_{n≡0(d)} λ = 0 ∀d) — shapes (a)/(a′) VACUOUS. The honest wall:
  **(b) ε-agreement** (exact on {prodPrimes, nu, totalMass} — the
  main term reads ONLY these; both errSums ≤ B) or **(c) the
  consumer-relative metatheorem** (∀ Φ with an explicit invariance
  hypothesis over the Agree relation, ¬(Φ certifies primes)) —
  (c) most faithfully renders the registered "exact class of
  consumers". The witness pair 1 ± λ is CONSTRUCTIBLE (weights ≥ 0);
  the output gap = 2·(prime mass in (z, x]). λ INVENTORY: mathlib has
  the bare definition + multiplicativity (2026 addition), NO
  summatory facts anywhere; Σλ = o(x) = 2 elementary nodes (ψ-PNT →
  M(y) = o(y) Tauberian bridge + the hyperbola fold) or a heavy
  L(s,λ) = ζ(2s)/ζ(s) port; the λ-BV (for the unconditional
  level-D version) is C/D-tier. THE CORPUS CONVENTION (EHall/
  PiAsymp-style named Props) permits the wall CONDITIONAL on a
  stated λBV Prop with zero porting — honest and idiomatic.

- 2026-07-15 ~09:30: **Q5a COMPLETE — outcome: OBSTRUCTION-PRECISE +
  a new delimitation theorem + Tao's open problem identified** (cost
  ≈ 243k tokens / 49 tool uses / ~36 min; 1 web check + 2 numeric
  scripts + 4 build cycles). Landed (Salt/TwinBar/Constrained.lean,
  11 decls, wired): twin_bar_constrained (the honest constrained
  bound), **no_twin_weight_constrained** (the no-go below δ₀ at the
  honest class, tent-witnessed non-vacuous),
  **cs_bound_ignores_constraint** (THE OBSTRUCTION AS A THEOREM: the
  identical bound holds with no marginal hypothesis — the per-slice
  CS never consumes the constraint; the wing weight reaches 2(1+δ)
  and β-optimality shows no base-tuning beats it — method-intrinsic).
  THE DISCOVERY: Q5a's full form IS Tao's open problem (Polymath8b
  VII, k=2 GEH: "We suspect... negative, but have not formally ruled
  it out"). Numerics (two methods, unconstrained control validates):
  c(δ) = 1.61/.2, 1.80/δ₀, 1.94/.7, 1.99/.9, **2.00000 at δ = 1**
  (grid-independent) — the first quantitative map of the constrained
  sup; R4 cleared (a non-attained sup, no gate crossing). R3
  divergence recorded (registration's class vs Tao's exact ε-class);
  **FABLE ADJUDICATION: the atlas canonicalizes TAO'S class for
  literature-facing statements; the corpus-internal class kept with
  the a-fortiori bridge. OPEN Q5a-1 (= Tao's problem: c(δ) < 2 on
  (δ₀,1), c(1) = 2) is rung-∞ territory beyond the sprint timebox —
  Q5a reports as RESOLVED-AS-OBSTRUCTION with the open note.**

- 2026-07-15 ~10:15: **Q3-recon COMPLETE** (cost ≈ 97k tokens / 23
  tools / ~6 min): the ENTIRE gaps ≤ 12 chain consumes EHall at
  EXACTLY ONE LINE (FrontierM.lean:171), reducing to the landed
  HasLevel (3999/4000) — strictly weaker in FORM (single level +
  BV-shaped haircut; the honest caveat: θ ≈ 1 is EH-strength in
  DEPTH). Option (b) EH_min ⟹ H₁ ≤ 12 = 1–2 nodes of pure
  extraction; option (a) GEH_min ⟹ H₁ ≤ 6 = multi-quarter (the k=5
  moment keystones are Fin-5-hardwired ~9k lines; the enlarged SIEVE
  machinery confirmed absent; the GEH convolution Prop is Fable-tier
  statement design). **FABLE ADJUDICATION: Q3 executes as (b)** —
  gaps_le_twelve_of_hasLevel with the θ-caveat stated prominently;
  (a)'s scope map is Q3's obstruction note (and the post-release
  explicit12 triage input).
- 2026-07-15 ~10:20: **Q4 COMPLETE — VERDICT: UNRECORDED, a minor
  new theorem** (cost ≈ 136k tokens / 30 tools / ~11 min).
  WindowedBVStatement.lean lands the two literature-facing
  restatements (exact-application proofs; axiom-clean; wired). The
  sweep (10 families, URLs + could-not-verify appendix): explicit
  closed-form BV constants exist ONLY for Λ/single-variable
  (Akbary–Hambrook, Sedunova, arXiv:2510.10853); every bilinear/
  type-II BV is ineffective; the sharp unfactored mn ≤ T window is
  non-standard packaging. OUR FORM'S DELTA: the first bilinear,
  sharp-windowed BV with closed-form constants + the block-prime √D
  level. Honest framing: new effective PACKAGING, not a new
  asymptotic frontier.

- 2026-07-15 ~10:40: **Q2a (TB3-ASM) COMPLETE — M₃ < 2 UNCONDITIONAL,
  the atlas's SECOND delimitation theorem** (cost ≈ 413k tokens / 73
  tools / ~61 min / ~15 build cycles; the pilot's 300–500-line
  estimate held at 742 incl. docs). three_bar discharges P-C's single
  deferred gap; no_triple_weight lands via the conditional bridge.
  THE ARCHITECTURE (the calibration lesson): region-integral combine
  (∫_{R₃} w_m·F², one integral_add collapsed by w_sum_three ≡ 3/2)
  avoids nested reconciliation; the genuine 3-D reversal keeps t₁ at
  an extreme so the associativity wall is NEVER HIT — the awkward
  middle order routes through the cheap parametrized 2-D swap. Eight
  Lean friction notes recorded for the assembly genre (indicator_of_
  notMem rename; obtain-clears-hypotheses; by_cases over indicator_
  comp_right; explicit-lambda integrability types; uIcc = closed Icc
  forcing ≤-stated slice lemmas; lake env lean skips style linters —
  finish on lake build). Remaining Q2: (b) the k=4,5 atlas, (c) the
  H₁ ≤ 6 delimitation statement.

- 2026-07-15 ~10:50: **Q3 COMPLETE (as adjudicated: the (b) form)**
  (cost ≈ 95k tokens / 26 tools / ~8 min — the cheapest sprint
  question, as predicted). Salt/Twelve/GapsOfLevel.lean:
  **gaps_le_twelve_of_hasLevel (hPNT) (hLoD : HasLevel (3999/4000))**
  — the minimal-interface theorem; the diff from the landed chain is
  LITERALLY one deleted line (the recon's claim confirmed by
  construction); the EHall capstone recovered as a one-line instance
  (anti-vacuity); the θ-caveat stated prominently in both docstrings
  (minimality of FORM, not depth). The GEH_min-at-k=3 route's scope
  map (multi-quarter, two new C-clusters) stands as Q3's obstruction
  note and the explicit12 post-release triage input.

- 2026-07-15 ~11:10: **Q6a-GATE — GO_W_CORRECTIONS; three tears
  caught pre-freeze + THE UNCONDITIONALITY AMENDMENT** (cost ≈ 128k
  tokens; numeric verification included). (1) The ≤ z tear: sifting
  p < ⌊√x⌋ lets z² survive with weight 2 whenever z is prime —
  siftedSum₊ = 2 FALSE on an unbounded set (verified x = 25/49/169);
  ∀ᶠ does not rescue it. (2) The dead-hypothesis tear: concluding on
  sPlus never uses invariance — the wall must conclude on sMinus.
  (3) The inhabitation tear: exact invariance admits only trivial
  certificates; the tolerant 2B form is inhabited by the landed
  Rosser floor but kills the fixed-3 corollary → the vanishing-
  proportion form + the CONCRETE CORE (V(sMinus) ≤ 2 + B vs sifted
  mass 2·(π(x) − π(√x)) — no abstract Φ, inhabited by construction).
  (4) THE AMENDMENT: total multiplicativity reduces the a = 0 class
  POINTWISE (Σ_{d∣n} λ = λ(d)·M_λ(⌊x/d⌋)) — no λ-BV ever needed; the
  effective summatory rate suffices and is reachable from the LANDED
  siegelWalfisz_psiTot via two bridge nodes ⟹ **THE WALL SHIPS
  UNCONDITIONAL** (the design's conditional-Prop route retired). All
  corrections applied to q6a-design.md; Q6a-1 ∥ Q6a-3 dispatched.

- 2026-07-15 ~13:10: **Q6a-1 COMPLETE — the witness pair lands, first
  attempt** (cost ≈ 199k tokens / 57 tools / ~26 min, Opus).
  Salt/TwinBar/ParityWall.lean (439 lines): nuDiv (ν(d) = 1/d, mult,
  0 < ν(p) < 1); **sPlus/sMinus : BoundingSieve** at the gate's ≤ z
  fix via mathlib's `primorial` (P(⌊√x⌋) = ∏_{p ≤ ⌊√x⌋} p), weights
  1 ± λ(n); the evaluations **siftedSum (sPlus x) = 2** and
  **siftedSum (sMinus x) = 2·(π(x) − π(√x))** (x ≥ 2) via the
  survivor analysis (minFac² ≤ n forces p ≤ ⌊√x⌋ ∣ P forward; p ∤ P
  reverse; survivors = {1} ∪ primes(√x, x]); **the pointwise a = 0
  identity lambda_mult_sum** (Σ_{n≤x, d∣n} λ(n) = λ(d)·M_λ(⌊x/d⌋), no
  coprimality — total multiplicativity) with rem bounds |rem d| ≤
  1 + |M_λ(⌊x/d⌋)| on BOTH instances; **SieveAgree** (D2 verbatim) +
  sieveAgree_pair (main fields rfl-equal); D5.3 numeric sanity
  compiled by `decide` (x = 100: 2 and 42 = 2·(25 − 4)). Ceremony:
  wired into TwinBar/All.lean + the six keystones added to the
  build-time #audit_axioms block — full build exit 0, all ✓
  [3 axioms]. Q6a-2 unblocks when Q6a-3 (in flight) delivers the
  M_λ rate.

- 2026-07-15 ~11:20: **Q2bc-RECON COMPLETE — k=4 GO, k=5 carrier
  mismatch mapped, R3 EARLY STOP on the literal "H₁ ≤ 6"** (cost ≈
  158k tokens / 17 tools / ~10 min, Opus). (1) **k=4**: the β-tuning
  extends mechanically (β = 1/3, c₄ = (4/3)log4 ≈ 1.8484 < 2); the
  analytic core is A/B-tier mirror work (N4-CORE); the assembly needs
  a size-s parametrization of the ENTIRE 3-D reduction layer (the
  4-simplex slices to a size-(1−t₁) 3-simplex — the 3-D file is
  hardwired to size 1) → three nodes N4-ASM-a/b/c, riskiest =
  N4-ASM-a (size-s 3-D reductions, C-tier, critical path for J₃/J₄);
  est. ~1200–1700 lines / 700k–1M tokens aggregate — assembly debt
  MAY extend past the sprint (registration permits). (2) **k=5**: the
  landed M5_cert (Salt/Twelve/Certificate.lean:265) is an EXACT ℚ
  bilinear ratio on Poly (191881/95820 ≈ 2.00251 > 2) — NOT the real-
  integral functional; a single-object bracket 2 < M₅ ≤ (5/4)log5
  needs the k-D real Dirichlet-integral bridge (does not exist in the
  corpus) + a full 5-D real assembly (~5–8 nodes) — OUT OF SPRINT
  SCOPE; the honest asymmetric form (ℚ witness > 2 landed; real upper
  bound as recorded debt) recommended. (3) **Q2c**: the literal
  "H₁ ≤ 6 delimitation" is NOT formable from landed material — it
  conflates the no-go atlas (no gap number), the k=5 certificate
  (gives ≤ 12 at BV, not ≤ 6), and the GEH/enlarged-k=3 floor whose
  sharp half IS Tao's open problem (rung-∞). RECOMMENDED REFRAME
  (user sign-off pending): the least-k theorem — "in the unmodified
  Maynard–Selberg class the least k with M_k > 2 is 5" (needs only
  the M₄ leg) + the honest gap companion "k=5 delivers H₁ ≤ 12 at
  BV-level" + an open note for the ≤ 6 optimality. N4-CORE dispatched
  (safe under every reframe); N4-ASM scheduling + k=5 debt + the Q2c
  reframe = user decisions.

- 2026-07-15 ~11:50: **N4-CORE COMPLETE — the k=4 analytic core,
  first attempt** (cost ≈ 106k tokens / 13 tools / ~8 min, Opus —
  cheaper than the recon's 120–180k estimate).
  Salt/TwinBar/FourBar.lean (443 lines): carriers R₄/I₄/J₁₄..J₄₄
  (marginal-innermost, ThreeBar convention); weights w₁₄..w₄₄ with
  w_sum_four ≡ 4/3; logWeight_third (∫ (a/3+t)⁻¹ = log 4);
  log_slice_CS_third + the four sliceCS lemmas (interval_CS reused
  verbatim); the numeric atom four_thirds_log_four_lt_two via
  log 4 = 2 log 2 + log_two_lt_d9 (cheaper than the k=3 exp route);
  FourBar as the named Prop + no_quad_weight_of_fourBar (modulo
  N4-ASM, exactly the k=3 heart pattern). Friction: namespace-clash
  avoidance vs ThreeBar's un-suffixed names (executor pre-renamed;
  confirmed no clash at the wired All.lean build); 4-tuple
  right-nesting projections fine under fun_prop. Ceremony: wired +
  13 keystones in #audit_axioms — full build exit 0, all ✓
  [3 axioms]. The M₄ leg of the least-k theorem (amendment A1) now
  rests only on N4-ASM-a/b/c (gated on the parity wall closing).

- 2026-07-15 ~12:00: **Q6a-3 LANDS NODE 2; NODE 1 STOP-AND-FLAGGED —
  the wall is currently CONDITIONAL on one clean Prop** (cost ≈ 340k
  tokens / 83 tools / ~53 min, Opus; ~10 build cycles).
  Salt/TwinBar/LambdaRate.lean (581 lines). LANDED: the identity
  λ = 1_squares ∗ μ (liouville_eq_chiSq_mul_moebius, via
  eq_iff_eq_on_prime_powers); the UNCONDITIONAL summatory fold
  Mlambda_eq_sum_Mmu (M_λ(y) = Σ_{d≤√y} M_μ(⌊y/d²⌋) — derived from
  scratch; mathlib has NO hyperbola/summatory-convolution lemma,
  recorded as a mathlib TODO); **Mlambda_rate** (the M_μ→M_λ rate
  fold, C' = 2C·4^A + 1, small-range/tail split at d = y^{1/4}) +
  **LambdaSummatory_of_MmuRate** — both conditional ONLY on the new
  Prop **MmuRate** (|M_μ(y)| ≤ C·y/(log y)^A). STOP-AND-FLAG (node
  1): deriving MmuRate from the landed siegelWalfisz_psiTot is the
  effective "equivalent forms of PNT" step — needs μ·log = −(Λ∗μ) +
  an Abel/bootstrap layer, several hundred lines, its own C-node
  (mathlib has only the bare moebius def; no summatory facts). The
  executor landed the fold rather than sink the budget — correct
  per the give-up-early rule. CONSEQUENCE: the wall ships
  conditional on MmuRate until the flagged node (Q6a-4, design pass
  = house) lands; still a massive improvement over the retired λ-BV
  route (one clean PNT-strength Prop vs a full equidistribution
  family). Ceremony: LambdaRate wired as the canonical owner of
  Mmu/Mlambda/MmuRate/LambdaSummatory; ParityWall's byte-identical
  local Mlambda dropped (the pre-mapped merge, house surgery); five
  keystones in #audit_axioms — full build exit 0, all ✓ [3 axioms].
  Q6a-2 DISPATCHED (the concrete core + the tolerant wall).

- 2026-07-15 ~12:20: **Q6a-4-RECON COMPLETE — R-b (Perron/1/ζ)
  recommended, GATED on the one missing keystone** (cost ≈ 167k
  tokens / 27 tools / ~12 min, Opus). Inventory: the SW contour
  spine is GENERIC at the Kernel/ContourShift/riesz_tsum_eq level
  (reused verbatim) and ψ-hardwired only from the composite identity
  down; 1/ζ is SIMPLER than −ζ′/ζ (mathlib has L(μ) = 1/ζ directly;
  |μ| ≤ 1 domination trivial; NO pole at s = 1 — no residue, no main
  term, rectBI = 0 closes the shift). R-a (the elementary Landau
  bootstrap): mathlib has Abel summation + all the μ/Λ convolution
  identities (L1–L3 are B-tier), but L4's naive insertion is
  CONFIRMED circular/false (the x·Σμ(d)/d term couples back to M(x)
  — verified on two splits; the term-by-term form cancels the LHS
  log exactly); the honest every-A iteration is C-with-D-risk.
  **THE FINDING: Rb-4 (|1/ζ| ≤ poly-log T on the zero-free box) is
  the whole ballgame** — absent from the corpus, and the landed
  ζ′/ζ box bound (O(log²T) via M0zeta) exponentiates to a
  SUPER-POLYNOMIAL |1/ζ| bound the kernel decay cannot absorb (the
  false-intermediate failure mode, caught at recon on the R-b side).
  The honest route needs a ONE-power ζ′/ζ segment bound near σ = 1
  (Titchmarsh 3.11-grade) or a poly-log Euler-product base at
  σ = 1 + 1/log T. VERDICT: Rb-4 sub-recon/design-gate dispatched
  (can the landed Blaschke/zero-count apparatus reach one power?);
  if Rb-4 prices D, BOTH routes are effectively D and the wall
  stays conditional on MmuRate as recorded debt (an acceptable
  registered outcome).

- 2026-07-15 ~12:45: **Rb-4 SUB-RECON: VERDICT D — Q6a-4 CLOSES AS
  RESOLVED-AS-OBSTRUCTION; the wall's MmuRate conditionality is
  REGISTERED DEBT per the pre-declared rule** (cost ≈ 150k tokens /
  19 tools / ~13 min, Opus). The audit PINNED the two-power loss to
  one step: hSumNorm (ShiftTrivChar.lean:272–282) bounds the zero
  sum by count × uniform 1/w — count O(log T) × w ~ 1/log T =
  log²T; the reduced log-derivative itself is already one-power.
  Beating it needs the harmonic decay of Σ 1/|t−γ|, i.e. THE LOCAL
  ZERO DENSITY #{ρ : |Im ρ − t| ≤ u} = O(u·log T + log T) — which
  fixed-radius Jensen STRUCTURALLY cannot give (the thin set is a
  full-height box, not a disk; no Jensen center exists near Re = 1
  for lack of a |ζ| lower bound), and which classically requires
  argument-principle N(T) machinery — absent from corpus AND
  mathlib. The Euler-product 3-4-1 base (landed) does NOT avoid it:
  the leftward transport integral consumes the same density. Both
  MmuRate routes are therefore effectively D. THE DEBT, PRECISELY:
  land effective N(T)/local zero-density (a multi-node C/D wave) OR
  any other route to MmuRate; the only opportunistic C-node worth
  noting is N1 (|ζ| ≤ C log T near Re = 1, Titchmarsh 3.5-grade,
  reuses the dTerm/zeta_shift scaffolding, ~200–300k) — reusable
  but does NOT unblock the wall alone. NARRATIVE NOTE for the
  report: the refutation engine ran three layers deep on its own
  design (Q6a-3 flag → Q6a-4 recon killing both naive routes →
  Rb-4 killing the honest-looking route) and terminated at ONE
  missing classical theorem, stated exactly — total probe cost
  ≈ 317k tokens, zero executor tokens burned on a dead route.

- 2026-07-15 ~13:20: **Q6a-2 COMPLETE — THE PARITY WALL IS LANDED;
  Q6a CLOSES** (cost ≈ 425k tokens / 80 tools / ~65 min, Opus; one
  serious pass, ~12 build cycles). Salt/TwinBar/Wall.lean (652
  lines): the budget lemmas (rosserRemainder ≤ ⌊√x⌋ +
  C·x(1+log x)/(log x)^A under LambdaSummatory); **the concrete core
  rosser_floor_undershoot — UNCONDITIONAL** (V(sMinus) ≤ 2 +
  errSum(sPlus) vs sifted mass 2(π(x)−π(√x)), pure algebra off the
  landed floor); **parity_wall** (tolerant, concludes on sMinus,
  2 + 2B) + **parity_wall_effective** (explicit budget under
  MmuRate); **no_parity_beating_certificate** (the
  vanishing-proportion punch, full asymptotic argument —
  Chebyshev.pi_ge + three limit lemmas); phiLowerR inhabitation
  (tolerance UNCONDITIONAL; certificate modulo hsupp). TWO HOUSE
  ADJUDICATIONS (both accepted): (1) the Rosser support bound
  errSum ≤ rosserRemainder is UNLANDED and its naive form
  (rosserCond → d < D) is FALSE for the lower sieve (the
  odd-position prime) — the executor delivered the honest errSum
  form for the concrete core and the design's 2+2B undershoot via
  the wall route, which reads rosserRemainder directly;
  phiLowerR_certificate carries hsupp explicitly (satisfied by the
  landed concrete Rosser instantiations; a small future node could
  discharge it generally). (2) The per-x √x-level tolerance form is
  only trivially inhabited — the FIXED-level-D form is canonical
  (the third instance of the exact-vs-tolerant lesson; recorded).
  Ceremony: wired + 11 keystones — full build exit 0, all ✓
  [3 axioms]. **Q6a FINAL SHAPE: the wall + undershoot landed;
  analytic budget conditional on MmuRate (registered debt,
  Rb-4 verdict D); the witness pair, evaluations, tolerance
  structure, and concrete core unconditional.** N4-ASM unlocked
  per amendment A1 (the wall closed first) — gate dispatched.

- 2026-07-15 ~13:40: **Q1 CHECKPOINT RATIFIED (JYH: "let's do full
  in-sprint")** — Chen-2 (chen_goldbach, the Goldbach form: every
  sufficiently large even N is p + P₂) will be PROVEN in-sprint; the
  reuse coefficient ships MEASURED, not census-predicted. Immediate
  consequence for the flagship: the "both of Chen's theorems"
  headline restructure is live (title/abstract/intro at the last
  responsible moment, per the drafting policy). Pipeline: Q1-INV
  (declaration-level mirror map, dispatched) → the Fable design
  freeze (wave plan + the three re-derive nodes) → adversarial gate
  → mirror waves. The recon census stands as the prediction to test:
  ~63% verbatim / ~35% parametric-mirror / ~1–2% re-derive (the
  N-dependent density + singular series, the CRT residue witness,
  the ∀N uniformity).

- 2026-07-15 ~14:05: **N4-ASM-GATE: GO_W_CORRECTIONS — the J₃₄
  peel-order tear caught pre-dispatch; all four corrections applied**
  (cost ≈ 142k tokens / 9 tools / ~15 min, Opus). THE TEAR (gate
  confidence ~90%, permutation analysis + cross-check against
  ThreeBarAsm's actual swap mechanism): J₃₄'s carrier order
  (t₄,t₂,t₁ outers, t₃ innermost) reaches NEITHER size-s reduce3
  order without swapping a MARGINAL — which needs a size-s
  marginal-continuity lemma that exists nowhere (ThreeBarAsm never
  swaps a marginal) and was unbudgeted; the design's own node-b line
  ("J₃₄ via peel-t₁-outer") was internally inconsistent with the
  carrier (t₄ outermost — the peel cannot start). Numerics CANNOT
  catch this genre (the region identity is order-agnostic Fubini) —
  the peel-order audit was the load-bearing check. FIX (the
  pre-authorized free choice): J₃₄ reordered to outers (t₁,t₂,t₄) in
  FourBar.lean (~10 lines, J₃₄ def + nonneg; sliceCS₃₄ and the
  no-go are order-independent; full build exit 0). Also applied:
  node-a signatures PINNED in the design (Δ₃ s, canonical/w3order
  _eq_region₃ s — the a→b interface de-risked); the two
  slice-continuity lemmas listed with owner node a; Δ₃_one_eq_R₃
  s=1 regression anchor added; J₃₄'s novel route pinned to node b.
  Gate also verified: s=0 non-pathological, s=1/2 numeric Fubini
  agreement (3 orders, 0.03020833), s=1 recovery clean, the 2-D
  layer already fully size-parametrized (reused verbatim), four_bar
  TRUE + inhabited on an asymmetric F (sumJ 0.5627 ≤ 0.7188).
  N4-ASM-a DISPATCHED (post-correction).

- 2026-07-15 ~14:50: **Q1-INV COMPLETE — the census VALIDATED at
  declaration level; the re-certification risk RESOLVED: NONE
  NEEDED** (cost ≈ 256k tokens / 42 tools / ~20 min, Opus; spine
  read personally + 4 deep-read subagents). (1) Target statement
  recommended: `∃ N₀, ∀ N ≥ N₀, Even N → ∃ p q, N = p + q ∧ p.Prime
  ∧ IsP2 2 q` (additive form, explicit threshold, IsP2 2 unchanged —
  no carrier N-parametrization anywhere). (2) THE KEY FINDING: the
  singular series 𝔖_N = ∏_{q|N,q>2}(q−1)/(q−2) enters ONLY through
  W (the sifted primes exclude q|N), and X_W = totalMass·W is the
  COMMON factor of all three razor carriers — it cancels in the
  normalized bracket; nuChen = 1/φ(d) never sees the residue; c̄ is
  a dimensionless integral over the fixed exponents [1/8,1/3];
  CbarCert/SuperPanels/razor_scalar_margin reused VERBATIM. (3) The
  three re-derive items priced DOWN: (i) B not C (the {q∤N}
  primorial + reduced-residue re-threading + a W-ratio residual
  ≤ ω(N)·N^{−1/8} absorbed by existing slack); (ii) B (the CRT
  witness avoiding {0, N mod q}, nonvacuous at q ≥ 3); (iii) A/B
  (opQ is a FIXED constant — opEps = 2/10⁸ — so opQ ≤ log N for
  N ≥ e^{opQ}; the ∀N wrapper is SIMPLER than the twin infinitude).
  (4) Riskiest node: G-SW — the {q|N} unit seam in the switched
  remainder (SwitchBV:88 + AggCE:75), the ONE genuinely new
  casework site (finite x^{o(1)} exceptional-modulus split). (5)
  Wave plan W0–W4, ~11 nodes, est. ≈2.9M tokens (→ ~2.2M if the
  rfl-transfer productivity holds). Two marked uncertainties (the
  hWy numeric closure at op point; G-SW cost read at signature
  level) + a W0 obligation (confirm the live spine =
  ChenTheorem ← FinA3c/FinLed3 ← Headline4 ← Assembly before
  mirroring). Design freeze (Fable) next → gate → waves.

- 2026-07-15 ~15:10: **N4-ASM-a COMPLETE — the risk node lands
  FIRST-BUILD-CLEAN at half budget** (cost ≈ 174k tokens / 24 tools
  / ~20 min vs the 350k budget, Opus). Salt/TwinBar/SimplexS.lean
  (380 lines): the size-s 3-D reduction layer — Δ₃ s + geometry
  (closed/compact/measurable), Δ₃_one_eq_R₃ by rfl (as the gate
  predicted), psi_eq₃, region_integrable₃, the two keystones
  canonical_eq_region₃/w3order_eq_region₃, outer marginals, the two
  gate-assigned slice-continuity lemmas (slice_fix₄_fst/snd) + the
  public slice_fix_fst₃ engine (deliberately exposed for node b's
  J₃₄ in-node swap). PINNED SIGNATURES CONFIRMED byte-compatible
  (#check-verified); s = 0 regression compiled (le_refl 0 — no
  lemma strengthens to 0 < s); s = 1 examples discharge the landed
  size-1 shapes via Δ₃_one_eq_R₃, nothing refactored. The predicted
  s-proliferation was 100% mechanical (the pre-parametrized 2-D
  layer made it transcription). FLAG for node b: ThreeBarAsm's 2-D
  Δ geometry is PRIVATE — re-derive locally if needed (node a did,
  as private Δ_measurableSet'). FRICTION CORRECTION to the Q2a
  note: `lake build` DOES enforce the 100-column longLine linter
  (and unusedVariables fires on explicit hypotheses — underscore
  them); byte-counting tools over-read Unicode lines, count
  codepoints. Ceremony: wired + 13 keystones — full build exit 0,
  all ✓ [3 axioms]. N4-ASM-b DISPATCHED on the byte-locked
  interface.

- 2026-07-15 ~13:35: **Q1-GATE: GO_W_CORRECTIONS — the X_W
  cancellation PASSES AT PROOF LEVEL; the G-SW seam VANISHES; one
  real correction** (cost ≈ 179k tokens / 28 tools / ~17 min, Opus).
  (1) ATTACK 1 (the load-bearing fact) SOUND: razor_of_normalized +
  hledger_at_certs take XW as a FREE positive real (the razor is
  XW-agnostic); totalMass = (ΣΛ)/φ(Q) is 𝔖_N-free; 𝔖_N lives only
  in W (the modulus); the c̄ count bridge's tripleSum is a pure
  N-free triple count; 𝔖_N cancels in Wy/Wz (both W's from the same
  modulus family). The dimensionless margin survives UNCHANGED;
  fchain_A1_final confirmed DEPTH-UNIFORM (∀ N ≥ 2, ∀ s ∈
  [3.9992,4]) so the Goldbach maxDepth is covered. The
  no-recertification verdict HOLDS at proof level. (2) ATTACK 2:
  the {q∣N} unit seam VANISHES (goldPs excludes q∣N ⟹ Coprime N d
  free on all d∣Ps; Q-level absorbed by G-RES; the AggCE crumb
  N-free) — G-SW downgraded from risk node, over-budgeted. (3) THE
  CORRECTION: W_ratio_upper's hwin hypothesis (window difference =
  ALL primes in [z,y)) is FALSE for Goldbach — G-DENS must prove a
  NEW window_prod_upper_punctured (prod_sdiff factoring + the
  exp(8/(z−2)) correction via ≤ 8 large prime divisors); numerics
  astronomically comfortable (e^{−4.25×10⁶} vs 1.26×10⁻³ slack),
  both directions checked. (4) The frozen statement passes (IsP2 2
  admits q prime; Even N load-bearing and correctly placed — for
  odd N the q=2 CRT class is correctly vacuous). Base spine
  axiom-clean. Corrections applied to q1-design.md. WAVES W0+W1
  DISPATCHED (G-IMPORT, G-DENS, G-RES, G-WEIGHT).

- 2026-07-15 ~13:55: **Q5b AXIS B COMPLETE — the conditional deficit
  + the kernel-checked self-funding no-go** (cost ≈ 164k tokens on
  the completing run / 25 tools; one API-drop resume mid-task —
  resumed at the checkpoint, no work lost). Salt/Chen/TwinDeficit.lean
  (595 lines, imports Assembly + RazorClose only). LANDED: the IsE2
  carrier + the exact split p2Ind = p1Ind + e2Ind; the honest
  P₁-razor p1RazorValue := p2RazorLHS − e2PrimeSum;
  **twin_razor_deficit** (≤ −δ·XW) conditional on TWO NAMED GAPS —
  GAP-U (an XW-scale UPPER bound on the sifted prime mass = the
  F-side Rosser chain at s = 4; the corpus has only the f-side
  lower) and GAP-E (a LOWER bound on the two-factor mass = a
  Chen-type semiprime count from below; the landed switching layer
  upper-bounds only) — plus the W-mirror at the live carriers.
  **THE STRUCTURAL FINDS (unconditional, kernel-checked): (1)
  deficit_floor_of_certs — the razor can NEVER fund its own deficit
  (any discharge needs e2lo ≥ 1/200 + δ, strictly above the razor's
  entire certified output); (2) heavy_semiprime_obstruction — on
  semiprimes with both factors > y, Chen's weight is identically 1
  with all three decorations zero: the E2-above-y mass is INVISIBLE
  to any retuning of the ½-coefficients.** The brief's hoped-for
  switching route refuted honestly (it upper-bounds the triple
  mass; the floor lemmas now make the inconsistent-hypothesis
  workaround impossible to write silently). R4 armed and CLEAR
  (witnesses certify finite positivity only). Axis sequencing
  verdict: the deficit lives in e2lo vs a1up, neither θ-dependent
  at leading order ⟹ DEFAULT C CONFIRMED (Axis A adds nothing B
  didn't). Ceremony: wired + 17 keystones — full build exit 0.

- 2026-07-15 ~14:00: **G-IMPORT (W0) COMPLETE — the backbone
  compiles as-imported; ONE SPINE SURPRISE** (cost ≈ 51k tokens /
  17 tools / ~5 min — under the 60k estimate, first attempt).
  Salt/Goldbach/Base.lean: the 11-module reuse surface + 5 smoke
  examples (razor_scalar_margin, cbar_lt, fchain_A1_final, IsP2
  prime disjunct, normalized_package) all reachable. SPINE FINDING
  (corrects the inventory): the live tail is Headline4 →
  **TheHeadline** → Assembly (TheHeadline is LOAD-BEARING, not
  superseded); and 7 of the 8 "superseded" capstones ARE in
  ChenTheorem's transitive import closure (via FinA3/AggSum/
  AssembleA3 stale imports) — import-closure ≠ proof-term
  dependence, but the claim as posed fails. HOUSE DECISION: no
  pruning of merged files now (hygiene-list item); G-ASM's brief
  will mandate MINIMAL imports for the mirrors (fresh files inherit
  nothing). Ceremony: Salt/Goldbach/All.lean created (house-owned
  aggregator) + wired into Salt.lean; full build exit 0 (8948 jobs).

- 2026-07-15 ~14:05: **THROTTLE POLICY (JYH-directed): max 4 active
  agents; work queues.** In flight at adoption: G-DENS, G-RES,
  G-WEIGHT, N4-ASM-b (= at cap). THE QUEUE (dependency-ordered,
  dispatched as slots free): 1. Q5b-C (weight-family optimality —
  A2's default-C confirmed by B); 2. N4-ASM-c (needs b); 3. G-A1,
  4. G-A2, 5. G-SW (need G-DENS); 6. G-COUNT, 7. G-BAND (W3);
  8. G-OP; 9. G-ASM (terminal). House work (design passes,
  ceremonies, ledgers) is not throttled.

- 2026-07-15 ~14:20: **G-WEIGHT (W1) COMPLETE — first attempt,
  strong reuse** (cost ≈ 102k tokens / 20 tools / ~11 min vs 80k
  estimate). Salt/Goldbach/WeightWindow.lean (171 lines): the three
  window-arithmetic mirrors under n+2 ↦ N−n. ADJUDICATED DEVIATIONS
  (both accepted): (1) the Goldbach window IS twinWindow N (the
  finset is literally identical; the value map differs) — no new
  def, avoiding a name collision; canonicalize goldbachWindow later
  if G-ASM wants the symbol. (2) window_two_thirds_lt's honest
  reflected shape: the twin's lower threshold x^{2/3} < n+2 does NOT
  reflect (the paired value runs over the BOTTOM half [2, N/2]) —
  the true bounds are 2 ≤ N−n ≤ (N+1)/2, verified against the
  consumer (chen_weight_struct at m = N−n). stripSum_le mirrored in
  full (the ∑1/p² telescope is N-free); switch_loss_le needs NO
  mirror (already stated for general N). Friction: the reflection
  n ↦ N−n is only InjOn the window (ℕ-subtraction saturates) —
  unlike the twin's globally-injective shift; beta-redex opacity vs
  omega (pre-build typed bounds). Ceremony: wired + 3 keystones +
  the Goldbach #audit_axioms block created — full build exit 0.
  Slot freed → Q5b-C dispatched (queue head).
