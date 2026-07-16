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

- 2026-07-15 ~14:35: **G-RES (W1) COMPLETE — first attempt** (cost
  ≈ 113k tokens / 22 tools / ~13 min vs 150k estimate).
  Salt/Goldbach/Residue.lean (184 lines, Mathlib-only — correctly
  upstream of the sieve files): exists_crt_finset (the reusable
  Finset-CRT engine), **goldbach_residue_witness** (the D2.2 frozen
  shape; per-prime choice r q = if N%q = 1 then 2 else 1; the q = 2
  case discharged by Even N — opQ IS even), crtClassG + modEq/
  coprime lemmas (byte-for-byte crtClassW mirror, the two "2"s
  become "N"), crt_class_coprimeG. ADJUDICATED DEVIATIONS (both
  accepted): (1) hQN : Q ≤ N added — MANDATORY (ℕ-truncation makes
  Coprime Q (N−a) vacuously false for a > N); free at the consumer
  (opQ ≤ log N). (2) Squarefree Q replaces the opf_Qfull mirror —
  strictly weaker hypothesis; NOTE FOR G-ASM/G-OP: supply
  Squarefree opQ at instantiation. Ceremony: wired + 6 keystones —
  full build exit 0 (8950 jobs). Queue state: slot open but heads
  blocked (N4-ASM-c needs b; W2 needs G-DENS — both in flight);
  active = G-DENS, N4-ASM-b, Q5b-C.

- 2026-07-15 ~14:50: **G-DENS (W1) COMPLETE — W1 CLOSES; the
  gate-corrected keystone lands + one executor catch** (cost ≈ 198k
  tokens / 28 tools / ~19 min vs 250k estimate; 1 serious attempt +
  2 trivial fixes). Salt/Goldbach/Density.lean (361 lines): goldPs
  (the punctured modulus, mirroring opP with ¬q∣N) + squarefree/
  primeFactors/odd facts; **coprime_of_dvd_goldPs** (the
  switch-seam-vanishing fact); the re-threading
  (coprime_mod_of_coprime — the class is N % d — +
  crtClass_coprime_gold); divisor_cases confirmed GENERIC (reused,
  not re-proven); **window_prod_upper_punctured** (prod_sdiff route
  exactly per the gate) + exp_correction_le_op (zr ≥ 10⁷ ⟹
  correction ≤ 1 + 2/10⁶) + the folded consumable form; goldPs_nu_eq
  (nuChen = 1/φ by rfl — N-independence confirmed at the kernel).
  EXECUTOR CATCH (adjudicated, accepted): the brief's card bound
  N ≤ zr^8 was BACKWARDS (zr = ⌊N^{1/8}⌋ gives zr^8 ≤ N) — the
  dischargeable form is (N:ℝ) < zr^9 ⟹ ≤ 8 divisors; G-OP must
  supply N < (opZ N)^9 (trivial at scale; route noted). Ceremony:
  wired + 17 keystones — full build exit 0 (8951 jobs). **W1
  reuse-coefficient row: est 480k across 3 nodes, actual 413k, all
  first-attempt.** W2 UNLOCKED: G-A1 + G-A2 dispatched (cap 4:
  N4-ASM-b, Q5b-C, G-A1, G-A2); G-SW queued.

- 2026-07-15 ~15:00: **Q5b-C COMPLETE, first attempt — ½ IS OPTIMAL,
  kernel-checked; Q5b CLOSES (B + C done, Axis A → DEBT per A2's
  commitment)** (cost ≈ 148k tokens / 24 tools / ~15 min vs 250k).
  Salt/Chen/WeightFamily.lean (288 lines, imports TwinDeficit only).
  THE FINDING: the ½ knob scales all three decorations identically;
  the margin is affine M(α) = 9779/10000 − K·α with K > 0
  (marginFn_linear/marginK_pos); admissibility (domination
  chenWeightA α ≤ 1_{P₂} at sifted points) forces α ≥ 1/2 EXACTLY —
  sufficiency from chen_weight_struct, necessity tight and
  non-vacuous at the concrete witness m = 30 (decoration sum exactly
  2). So **alpha_half_optimal: the landed ½ sits precisely on the
  admissibility boundary; everything larger strictly costs margin**
  (alpha_half_strict); the α = ½ regression recovers
  razor_scalar_margin. The family dies at α ≈ 0.50629
  (numeric-only — needs a c̄ LOWER bound the corpus lacks;
  honestly not claimed in Lean). **retune_invisible_at_heavy**
  (consuming Axis B's obstruction): the entire α-family collapses to
  the landed weight at heavy semiprimes — the deficit driver is
  identically blind to the knob. R4 clear. THE (z,y) GRID
  (numeric-only, scope-honest): the landed c̄/W-ratio/A₃ values
  reproduced exactly; NEW CONSTRAINT surfaced — b ≥ 1/3 is FORCED
  by the size lemma (m < (y+1)³ at m ≤ x), so the
  smaller-c̄ columns are inadmissible; within the admissible region
  the A₃-direct saving at (1/7, 3/8) is offset by both cascade
  terms moving against it — the landed (1/8, 1/3) reads as a
  cascade balance point; no superior point claimable without
  per-point re-derivation of f(s)/F(s)/the window cost. Ceremony:
  wired + 10 keystones — full build exit 0 (8952 jobs). **Q5b
  FINAL: Axis B (conditional deficit + two unconditional
  obstructions) + Axis C (exact optimality + invisibility + the
  b ≥ 1/3 constraint); Axis A (θ-crossover) = recorded debt.**
  Slot freed → G-SW dispatched (W2 head); N4-ASM-b stopped after a
  42-min hang mid-STEP-0 and RESUMED at its checkpoint.

- 2026-07-15 ~15:25: **G-A1 (W2) COMPLETE — first attempt, both
  files; the seam-vanishing realized; one load-bearing class
  correction** (cost ≈ 239k tokens / 45 tools / ~23 min vs 330k).
  Salt/Goldbach/A1.lean (372) + A1W.lean (414): the A₁ sieve pair
  (base + W/AP-class) with multSum/siftedSum/rem facts, the ℕ-sub
  divisibility bridge (dvd_sub_iff at n ≤ N — replaces the twin's
  d ≥ 3 shape), gold_A1_lower(_B)(_W)(_B_W), goldBVSum(_W),
  goldRosserRemainderW_le_split, W_goldA1_ge. REUSE CENSUS: ~75%
  verbatim-instantiation (the whole cB numeric τ-stack, the
  linear-sieve keystones, the BV dispersion engine, apDiscW,
  vratio_prod_le...), ~25% mirror, 3 genuinely new items. FINDING
  REALIZED: **divisor_cases is NOT needed at all** — the d-side
  coprimality is the uniform Coprime d N from the threaded
  Coprime P N; the twin's oddness disjunction AND the rem-1 special
  case both dissolve (single uniform branches). ADJUDICATED
  DEVIATION (load-bearing, accepted): **crtClassA1** — the A₁
  n-side class fuses a (mod Q) with N (mod d), reduced from
  Coprime Q a; crtClassG's N−a class is the SWITCH/A₂ class (the
  ledger sits at N−n there). Correct catch; G-A2/G-SW briefs
  already point at crtClassG. P stays abstract with hPN threaded
  (G-ASM instantiates at goldPs). Friction: the reflection InjOn +
  Finset.mem_coe pattern in every sum_image. Ceremony: wired + 8
  keystones — full build exit 0 (8954 jobs). W3 remains blocked on
  G-A2/G-SW; one slot open, queue heads dependency-blocked.

- 2026-07-15 ~15:45: **G-A2 (W2) COMPLETE — first attempt** (cost ≈
  249k tokens / 34 tools / ~25 min vs 280k). Salt/Goldbach/A2W.lean
  (572 lines): goldA2SieveW + facts, goldA2pW + per-prime bound
  (twin_A2_per_prime_B's engine hypotheses passed VERBATIM — zero
  Goldbach re-shaping), goldRosserRemainderW2_le_split,
  goldA2_hBVagg_W, crtClassGA (the A₂-side fused class a(Q) ⊗
  N(mod M) — distinct from both crtClassG and crtClassA1, the third
  class in the family, correctly). THE SIMPLIFICATION: the
  reflection makes d ∣ (N−n) ⟺ n ≡ N (mod d) — AP-membership of n
  DIRECTLY, weight Λ(n) unshifted; the puncture makes the class
  coprimality direct (divisor_cases eliminated again). BYTE-LOCK
  DEVIATION (downstream-critical): **goldA2_hBVagg_W aggregates
  over the PUNCTURED prime window** (p prime ∧ ¬p∣N) — the p∣N
  fibres are provably empty but the pointwise apDiscW_le fails on
  non-reduced classes; **G-COUNT must land on the same punctured
  set** (baked into its brief at dispatch). P kept abstract (hPcopN
  threaded); the GLU close rows byte-identical to the twin's.
  Ceremony: wired + 6 keystones — full build exit 0 (8955 jobs).
  W2 = G-A1 ✓, G-A2 ✓, G-SW in flight; W3 unblocks when G-SW lands.

- 2026-07-15 ~16:05: **G-SW (W2) COMPLETE — W2 CLOSES; the switch
  layer lands first-attempt with zero odd-d casework** (cost ≈ 299k
  tokens / 56 tools / ~30 min vs 350k, the pre-gate "risk node"
  budget). Salt/Goldbach/Switch.lean (647) + SwitchBV.lean (659):
  the four sieve instances (base/W/block/blockW) with ALL FOUR
  rfl-transfers holding (no carrier drift); the sharp cB keystones;
  the BV bridge at prod ≡ N (mod d); the full block-W
  identification chain at the landed crtClassG; the AggCE crumb +
  gold_hCE_at_op. THE SEAM, closed: gold_switch_coprime_N
  (hPsN → d ∣ Ps → Coprime d N) replaces switch_dvd_coprime_two —
  the gate's vanishing prediction, realized as a 2-axiom lemma.
  Genuinely new: goldTripleSet at the BOTTOM-half range [2, N/2]
  (the one structural novelty vs the twin's top half). BYTE-LOCK
  NOTES (downstream-critical): (a) G-SW OWNS the triple carriers —
  **G-COUNT prices them via import, never redefines** (dup-def
  clash); (b) gold_mainA3_of_hBVswitch takes the survivor bridge as
  a hypothesis — **G-ASM supplies goldTriplePrimeSum + the bridge**;
  (c) the a ≤ N saturation hypothesis threads the block-W chain
  (free at consumers via the witness's hQN). Ceremony: wired + 18
  keystones — full build exit 0 (8957 jobs). **W2 totals: est 960k
  / actual 787k, all first-attempt. W3 UNLOCKED: G-COUNT + G-BAND
  dispatched (active: N4-ASM-b, G-COUNT, G-BAND; one slot held for
  N4-ASM-c).**

- 2026-07-15 ~16:30: **G-BAND: STOP-AND-FLAG (the D5 ≥2× rule fires,
  attempt 1) — the band chain re-cut into four nodes; two S2 kernels
  landed as the down-payment** (cost ≈ 187k tokens / 20 tools / ~12
  min). THE MEASUREMENT: the terminal gold_hBVblocksW_discharge'
  chain is NOT carrier-generic — Chen.blockBox_windowDisc_eq_res
  (WindowSW:565) hard-wires the twin TOP-half window as a DIFFERENCE
  of two apDiscBilinCutoff cutoffs; goldTripleSet's BOTTOM-half
  window (G-SW's recorded novelty) reshapes the identification to a
  SINGLE cutoff — the box/band/diagonal chain is a genuine
  re-derivation (~1500–2500 lines: SwitchW2 1118 + PDiag 902 +
  BandIdent 751 + BandClose 492 + WindowSW), a wave not a node.
  LANDED (Salt/Goldbach/Band.lean, 92 lines, both keystones
  3-axiom): gold_dvd_sub_of_resG (the S2 divisibility at the
  reflected class — the ℕ-subtraction direction flips and is
  handled) + gold_diag_residue_crumb (the divisor-count residue leg,
  rough_divisor_crumb reused verbatim). VERBATIM-CONFIRMED: the
  whole bilinear/Kerr pricing engine + pair bijection + the diagonal
  N-free ingredients are generic (no mirror needed). RE-CUT ADOPTED
  (design table amended): G-WINDOWSW (C, de-risk recon FIRST — the
  single-cutoff reshape is the risk) → G-BANDIDENT (B) ∥ → G-SW2
  (B/C) → G-PDIAG (C, the terminal). Chen-2 grows 11 → 14 nodes;
  the estimate moves back toward the recon's original ≈2.9M (the
  early waves' savings partly spent here — the honest coefficient).
  Ceremony: wired + 2 keystones — full build exit 0 (8958 jobs).
  G-WINDOWSW-recon dispatched (the de-risk pass).

- 2026-07-15 ~17:00: **G-COUNT: STOP-AND-FLAG — THE DYADIC TEAR: the
  twin's count mechanism silently depends on its lower product
  bound; the constant survives, the MECHANISM doesn't** (cost ≈
  199k tokens / 32 tools / ~22 min; the flag fired during design
  analysis, before any wasted construction). THE FINDING, two-sided:
  (1) GOOD — the leading constant is UNCHANGED: the per-pair
  integral is byte-identical (same BJS weight, same N/2 factor,
  σ-range identical up to a log_N 2 → 0 endpoint), c̄ N-free —
  D1's no-recertification claim holds AT THE COUNT LEVEL and the
  bridge carries no 𝔖_N. (2) THE TEAR — the twin prices its
  p₃-count on a DYADIC interval (x/2p₁p₂, x/p₁p₂], forced by its
  lower product bound (2·prod > x), where the crude
  prime_count_Ioc_le already carries the sharp log weight. The
  Goldbach bottom-half has NO lower product bound → the interval
  (y, N/2p₁p₂] is non-dyadic; crude pricing overshoots by
  3(1−β−σ) ∈ [1, 13/8] — **which BREAKS the razor margin
  (0.4 − 1.6·0.363 < 0)**. Grinding would have landed a lemma too
  weak for assembly — the flag is the save. THE FIX (new Class-C
  keystone, ~150–250 lines): goldPerPair_pi_upper — the sharp count
  via p₃-dyadic-sum + geometric series against prime_count_Ioc_le
  (the mass concentrates at the top piece; no new PNT machinery).
  After it: weightedPairSum'_le_cbar reuses VERBATIM (carrier-free)
  and the chain composes to the same c̄/2. LANDED down-payment
  (Salt/Goldbach/Count.lean, 148 lines, 2 keystones): the
  projection reduction goldCard_le_pairSum + goldTripleSum_le_
  pairSum (via G-SW's carriers, zero redefinitions — byte-lock (b)
  honored; Lfun/pairSet' reused directly). RE-CUT: G-PIUPPER (C)
  DISPATCHED → G-COUNT-2 (the compose + op chain, mostly verbatim)
  follows. Chen-2 now ~16 nodes. Ceremony: wired + 2 keystones —
  full build exit 0 (8959 jobs).

- 2026-07-15 ~17:30: **G-WINDOWSW-recon: NO_GO on the single-cutoff
  premise — the de-risk gate catches the deepest tear of the arc
  pre-dispatch; FABLE ADJUDICATION: Opt-A (annulus-sliced reuse)**
  (cost ≈ 208k tokens / 19 tools / ~17 min, read-only). THE FINDING:
  the window IDENTIFICATION reshapes to a single cutoff cleanly
  (the lower boundary is VACUOUS — prod3 ≥ 8; A(1) = 0 identically)
  — but the PRICING does not compose: the generic pricers bound by
  the FULL box X·M with no T-dependence; the twin never pays that
  because box_disc_three_way cancels the two cutoffs off the
  dyadicBoundary (≤ 3 pieces, needing T₂ ≤ 2·T₁ — the twin's
  top-half window IS a factor-2 annulus). The Goldbach effective
  support [z·y², N/2] ≈ [N^0.79, N/2] spans ~21 dyadic scales —
  a monolithic cutoff pays X·M ≈ N^1.21 ≫ the N/(log N)^A budget,
  and the naive difference form fails the ≤-3-pieces lemma. THE
  TWO-CUTOFF STRUCTURE IS LOAD-BEARING (the exact
  shared-boundary-cancellation genre the brief asked about).
  ADJUDICATION (house): **Opt-A — the outer dyadic annulus sum**:
  slice [z·y², N/2] into factor-2 annuli; per annulus the twin's
  difference form + boundary reduction reuse VERBATIM at
  x_local = 2^{k+1}; the O(log N) annuli cost ONE log, absorbed by
  consuming the BV backbone at A+1 (free — SW supplies every A).
  No landed node re-opens. Opt-B (single annulus [N/4, N/2])
  REJECTED on a check the recon skipped: prod/N ratios [1/4,1/2] ≠
  the twin's [1/2,1] shift the BJS weight endpoints → c̄ changes →
  re-certification — worse than priced. HINDSIGHT NOTE (recorded
  for the taxonomy): a window-role FLIP at design time (sift n over
  [2, N/2], products land top-half) would have given the twin's
  ratios everywhere and avoided all three bottom-half tears — the
  lesson: mirror the INVARIANT (the product-window shape the
  mechanisms depend on), not the SURFACE (the n-window finset).
  Five landed nodes make the flip uneconomical now; Opt-A is
  strictly cheaper. G-WINDOWSW DISPATCHED on the Opt-A spec.

- 2026-07-15 ~17:35: **N4-ASM-b KILLED after a third
  monolithic-generation failure (no skeleton 30 min post-resume
  despite the incremental mandate) — RE-CUT into b1/b2 with fresh
  context** (the poisoned-context reset; sunk cost ≈ 2 failed runs).
  b1 = Δ₄ geometry + psi₄ + region_integrable₄ + marginals + the
  two PEEL-OUTER reductions (j3order/j4order, consuming SimplexS);
  b2 (queued behind b1) = the two peel-inner reductions (canonical4/
  j2order). Hard per-call line limits in both briefs. b1 DISPATCHED.

- 2026-07-15 ~17:55: **N4-ASM-b1 COMPLETE — the fresh-context re-cut
  + incremental discipline lands the peel-outer half first-attempt**
  (cost ≈ 170k tokens / 24 tools / ~17 min; the predecessor's two
  monolithic-generation deaths cost ≈ 2 lost runs — the process
  lesson is in the ~17:35 entry). Salt/TwinBar/Simplex4.lean (223
  lines): Δ₄ + geometry + Δ₄_eq_R₄ (rfl — the node-c bridge), psi₄
  (the slice-indicator identity both outer reductions consume),
  region_integrable₄ + outer_marg₄_fst/swap, and the two peel-outer
  keystones — **j4order_eq_region** (peel t₁ outer → w3order₃(1−t₁),
  no swap) and **j3order_eq_region** (the (t₄,t₃) swap at size
  1−t₁−t₂ via slice_fix_fst₃ ∘ slice_fix₄_fst, then routing THROUGH
  j4order — an economy the design didn't mandate but is strictly
  cleaner). Both reductions built FIRST TRY on node a's byte-locked
  interface — the pinned-signature discipline paying again. b2's
  interface (Δ₄/psi₄/region_integrable₄) byte-locked in the report;
  b2 needs the integrate-t₁-out marginal (the true psi_eq analogue)
  + slice_fix₄_snd — in its brief. Ceremony: wired + 10 keystones —
  full build exit 0 (8960 jobs). N4-ASM-b2 DISPATCHED.

- 2026-07-15 ~18:10: **Opt-A RATIFIED (JYH: "that's a good tradeoff,
  stay with Opt-A and keep going")** after the results-cost review:
  the theorem statement/unconditionality/axioms/c̄/margin are
  unchanged under either route; the costs are a modest inflation of
  the already-tower-grade N₀ (A ↦ A+1 absorption), a higher-but-
  more-informative measured reuse coefficient (the hindsight delta
  is registered as a finding, and the annulus + PiUpper machinery
  are reusable assets a flip would not have produced), vs the
  flip's re-opening of five ceremonied nodes on an un-reconned
  design belief. The window-flip lesson stands recorded for the
  taxonomy; no retrofit.

- 2026-07-15 ~16:35 (real ~15:40): **G-WINDOWSW COMPLETE — Opt-A
  vindicated first-attempt** (cost ≈ 285k tokens / 65 tools / ~31
  min vs 400k). Salt/Goldbach/WindowSW.lean (499 lines): the goldCut
  annulus family (T_k = min(2^k, N/2); goldCut_succ_le_two_mul IS
  the factor-2 hT slot — dyadicBoundary_card_le_three consumable
  per annulus); the general-cutoff identification (the twin's
  hard-wired (x, x/2+1) pair GENERALIZED to arbitrary (Tlo, Thi] —
  each annulus is a genuine window filter, the ±1 boundary worked
  honestly); the telescoping outer sum; the Φ_k reassembly ending
  at goldBoxHonestDisc_le_annulus_sum (the hHD analogue with the
  extra Σ_{k ≤ ⌊log₂N⌋} explicit — the ONE log Opt-A pays, now
  kernel-certified as ⌊log₂N⌋ + 1 annuli). REUSE MEASURED: ~60%
  verbatim/mirror, ~40% new annulus plumbing; the twin's PRIVATE
  pair-uniqueness lemmas had to be restated (the private wall
  again — third occurrence, now a standing pattern for the
  method paper). BYTE-LOCK for G-SW2: price each annulus via
  box_disc_three_way verbatim, consume BV at A+1; the box objects
  are OWNED here (import, never redefine). Ceremony: wired + 6
  keystones — full build exit 0 (8961 jobs). G-BANDIDENT DISPATCHED.

- 2026-07-15 ~16:50 (real ~15:55): **N4-ASM-b2 COMPLETE — node b
  CLOSES; the gate's marginal-continuity blocker met and resolved
  faithfully** (cost ≈ 210k tokens / 27 tools / ~23 min vs 300k;
  every declaration first-pass). Salt/TwinBar/Simplex4Inner.lean
  (248 lines): psi_eq₄ (the true integrate-t₁-out marginal);
  **reduce3_canonical_int** — the design call of the node: peeling
  t₁ inner produces the full marginal Φ whose CONTINUITY is exactly
  the unbudgeted lemma the gate flagged; the executor swapped the
  hypothesis to INDICATOR-INTEGRABILITY (from region_integrable₄
  via Fubini), which is how the 3-D template itself bottoms out —
  faithful, not a weakening; **canonical4_eq_region** (J₁₄) +
  **j2order_eq_region** (J₂₄, via slice_fix₄_snd +
  simplex_swap_param) + the two t₄-outer marginals node c needs.
  ALL FOUR reduction LHS orders match the FourBar carriers
  character-for-character; all four RHS share the identical
  Δ₄.indicator form. Node b totals (incl. the two dead monolithic
  runs): ≈ 470k vs the original 350k estimate — the overrun is
  entirely the process failure, not the mathematics (b1+b2 proper:
  380k, first-attempt each). Ceremony: wired + 7 keystones — full
  build exit 0 (8962 jobs). **N4-ASM-c DISPATCHED — the k=4 finale
  (the four peel bounds + four_bar + no_quad_weight).**

- 2026-07-15 ~17:10 (real ~16:05): **G-PIUPPER COMPLETE — the
  dyadic-tear keystone, CLEANER than the twin's mechanism** (cost ≈
  362k tokens / 75 tools / ~65 min vs 250k — the arc's first
  overrun: one coherent design, ~15 API-drift build iterations, no
  restart). Salt/Goldbach/PiUpper.lean (527 lines):
  **goldPerPair_pi_upper** — the sharp per-pair count over the
  non-dyadic (y, M] via full dyadic descent to y + per-piece
  crude pricing + telescoping/Abel: the correction is PURELY
  MULTIPLICATIVE, 1 + (4log2 + 16log3 + 32K)/log y, with **NO
  additive per-pair remainder** (the twin's +1/L₀ is gone — the
  Abel identity kills the piece floors). The overshoot is o(1),
  the razor-margin break avoided. Compiled regression: the summed
  form matches weightedPairSum' byte-identically ⟹
  **weightedPairSum'_le_cbar reuses VERBATIM** (as G-COUNT
  predicted). BYTE-LOCKS for G-COUNT-2: no additive remainder to
  thread; the correction lives in log y (not log Lval); two extra
  hypotheses (6 ≤ y, log N ≤ 3 log y — the operating relation).
  Ceremony: wired + 1 keystone — full build exit 0 (8963 jobs).
  G-COUNT-2 DISPATCHED.

- 2026-07-15 ~17:35 (real ~16:25): **G-BANDIDENT COMPLETE, first
  attempt** (cost ≈ 308k tokens / 97 tools / ~38 min vs 300k).
  Salt/Goldbach/BandIdent.lean (977 lines, 31 decls): the band
  rectangle↔cutoff identifications per-annulus (general (Tlo,Thi],
  free R₀); the window-free band close (goldBandCard_split,
  goldSymCard_two_mul via sum_symm_ordered_split INSTANTIATED
  VERBATIM, goldBandDiagCount_le, goldBandDiscW_eq_three); the two
  annulus-sum telescopes (both driven by WindowSW's generic
  goldWindowDisc_le_annulus_sum). Private wall — 4TH occurrence
  (the twin's private pair-uniqueness/summand lemmas restated).
  HOUSE CONFIRMATION of the executor's flag: the residue crumb
  (gold_diag_residue_crumb) belongs to G-PDIAG's aggregate, NOT the
  per-box count — the executor's combinatorial-projection reading
  of goldBandDiagCount_le is correct. Ceremony: wired + 11
  keystones.

- 2026-07-15 ~17:40 (real ~16:25): **N4-ASM-c COMPLETE — FOUR_BAR
  IS PROVED; M₄ < 2 UNCONDITIONAL; THE Q2b ASSEMBLY CLOSES** (cost
  ≈ 258k tokens / 42 tools / ~28 min vs 300k; 1 serious attempt,
  ~6 targeted cycles). Salt/TwinBar/FourBarAsm.lean (493 lines):
  the four peel bounds J₁₄..J₄₄_bound (the J₃₃_bound template one
  level up — triple-nested integral_mono + the landed sliceCS at
  the innermost slice + nodes a/b1/b2's marginals and reductions),
  the w_sum_four combine, **four_bar : FourBar** (the Prop
  discharged), **no_quad_weight : M₄ ≤ (4/3)log 4 < 2,
  UNCONDITIONAL** — the atlas's third delimitation. Friction: the
  Δ₄/R₄ defeq bridge under HO metavars (the have-coercion pattern);
  explicit (g := ...) on non-goal-pinned slice calls (the landed
  pattern). Assembly totals: a 174k + b1 170k + b2 210k + c 258k +
  2 dead b-runs ≈ 90k = **~900k vs the original 3-node 950k
  budget** — ON BUDGET despite the process failures, thanks to the
  gate + the pinned interfaces. Ceremony: wired + 7 keystones —
  full build exit 0 (8965 jobs). **THE LEAST-K CAPSTONE (Q2C-CAP)
  DISPATCHED: k = 2, 3, 4 closed + the ℚ certificate at k = 5 →
  the A1-ratified statement.** G-SW2 DISPATCHED (BandIdent landed).

- 2026-07-15 ~17:55 (real ~16:45): **G-COUNT-2: the c̄/2 close LANDS
  first-attempt + CATCH: the keystone's op-point satisfiability
  trap** (cost ≈ 248k tokens / 29 tools / ~17 min). LANDED
  (Salt/Goldbach/CountFinal.lean, 170 lines, 2 keystones):
  **goldTripleSum_le_cbar_final** — the (1 + C/log y)·(c̄/2)·
  (N/log N) close with weightedPairSum'_le_cbar consumed VERBATIM
  (the recon/gate prediction fully realized) — and the uniform-K op
  form. NO additive remainder (the Goldbach close is CLEANER than
  the twin's two-factor correction). The ec-margin arithmetic
  verified: the correction is absorbed with ~85× margin at the op
  threshold — the twin's error budget is nowhere near the blocker.
  **THE CATCH (executor refused to consume blind — the
  satisfiability discipline working at the executor tier):
  goldPerPair_pi_upper's hypothesis log N ≤ 3·log yN is JOINTLY
  UNSATISFIABLE with the op point's yN = ⌊N^{1/3}⌋ for every
  non-cube N** (fails by ≤ 3·N^{−1/3}) — a PROOF ARTIFACT in
  PiUpper's hND_le_ly (the loose logND ≤ log N − log y, ignoring
  p₁ ≥ z; the true logND ≈ (13/24)log N has room). The executor
  did NOT write a vacuous CountOp; flagged keystone-tier. HOUSE
  ADJUDICATION: statement-weakening fix (dropping/weakening a
  hypothesis STRENGTHENS the theorem — permissible on the
  exploration file with the fix note recorded); G-PIUPPER-FIX
  dispatched (reprove hND_le_ly via p₁ ≥ z, drop hlogN, keep the
  signature otherwise byte-stable, re-verify the regression).
  W-side assessment recorded: the equidist fiber mirror is
  Class-C-sized (the reflected/punctured bijection differs
  genuinely); the recommended terminal path avoids it (the direct
  tripleSum/φ seam via corr_le_at_op once the fix lands). Ceremony:
  wired + 2 keystones — full build exit 0 (8966 jobs).

- 2026-07-15 ~18:10 (real ~16:55): **Q2C-CAP COMPLETE —
  least_k_theorem LANDS; SPRINT QUESTION Q2 CLOSES** (cost ≈ 128k
  tokens / 21 tools / ~4 min; first-attempt, all proofs one-line
  re-exports as designed). Salt/TwinBar/LeastK.lean (139 lines):
  maynard_closed_at_two/three/four (the uniform-named no-go
  re-exports with the c_k = (k/(k−1))log k caps),
  maynard_open_at_five (2 < ΣJcal/Ical on Fstar, via M5_cert —
  chosen over theta_ratio_cert as the headline-clean wrapper), and
  **least_k_theorem** — the A1-ratified 4-way conjunction with the
  carrier asymmetry documented prominently (continuous no-gos ×3 +
  the exact ℚ certificate at k = 5; the Dirichlet bridge =
  registered debt), the numeric atlas (1.386/1.648/1.848 < 2 <
  2.00251), and the H₁ ≤ 12 + ≤ 6-open companion notes as
  docstring pointers. Ceremony: wired + 5 keystones — full build
  exit 0 (8967 jobs). **Q2 FINAL: (a) TB3-ASM ✓ M₃ < 2; (b)
  N4-CORE + N4-ASM-a/b1/b2/c ✓ M₄ < 2 unconditional; (c) the
  least-k theorem ✓ under amendment A1; k=5 upper bound + the
  Dirichlet bridge = registered debt. SPRINT SCOREBOARD: Q2 ✓ Q3 ✓
  Q4 ✓ Q5 ✓ Q6a ✓; Q1 at 12/16 nodes; Q6b design block = the
  remaining slate item.**

- 2026-07-15 ~18:30: **POST-SPRINT DIRECTIVE (JYH): "we should
  revisit local-zero-density when we are done with the sprint"** —
  the N(T)/local-zero-density design arc (the Rb-4 verdict-D debt;
  discharging it makes the parity wall unconditional and unlocks
  zero-density technology) is RATIFIED as the first post-sprint
  work item. The route per the D-conversion doctrine: a Fable
  design arc decomposing Riemann–von Mangoldt into gated C-nodes
  (the SW-contour-arc pattern), not a D dispatch. Queued ahead of
  the release lane's remaining items.

- 2026-07-15 ~18:35: **Q6b-RECON COMPLETE — the door has a
  freeze-ready shape and a THEOREM-LEVEL DICHOTOMY close** (cost ≈
  168k tokens / 32 tools / ~8 min). THE HINGE (deliverable 1): the
  wall's tolerance quantifies over everything the main term +
  pooled |·|-budget can see; the ONLY escaping read is the SIGN of
  the weights inside multSum (the λ ↦ −λ involution preserves
  SieveAgree — the |rem| bounds are literally identical on the
  pair); Chen's switch is the kernel-checked proof-of-life that a
  certificate CAN read at signed resolution (the α⊗β bilinear
  decomposition). THE CENSUS (deliverable 2, brutal per the Q5a
  lesson): (i) the FI-style twin type-II form — the ‖·‖ upper half
  is LANDED (windowed_bilinear_BV), the twin implication crosses to
  open exactly at upper→asymptotic-lower (the P₁ lower sieve, the
  large-sieve level-1/2 wall); (ii) TwinLambda (λ(n)λ(n+2)
  cancellation over the landed Liouville carriers) — beautiful but
  open on BOTH premise (fixed-shift Chowla) and implication (zero
  λ→Λ transfer) — board sibling, NOT the door; (iii) Heath-Brown/
  Siegel — needs the same N(T) stack Rb-4 verdict-D'd, and is the
  wrong genre (doesn't go through the sieve interface) — board
  sibling. RECOMMENDATION: freeze (i) as TwinB_min := ∃ θ > 1/2,
  TwinTypeII θ (the MAIN-TERM-carrying twin bilinear asymptotic
  over apDiscBilinCutoff/p1PrimeSum); ship TwinB_min ⟹
  TwinPrimeConjecture at B/C (the main term dominates + the landed
  survivor endgame re-pointed); **the wall∧door DICHOTOMY as a
  cheap corollary of the landed no_parity_beating_certificate:
  every lower-bound certificate is EITHER SieveAgree-tolerant (and
  parity-blind — the wall) OR a signed-weights reader (the door)**;
  anti-vacuity incl. the twinSingularSeries > 0 obligation (the
  F≡1 alarm: a zero main term must not satisfy the Prop) and the
  R4 discipline (a level-θ asymptotic with explicit saving, never
  a raw lower bound). The deep D-gap (proving TwinB_min) is
  STATED-NOT-ATTEMPTED = flagship Challenge 2 + board entry #2.
  Est. in-sprint total ~430–630k (gate + one B/C executor).
  DESIGN FREEZE next (house), then the gate.

- 2026-07-15 ~18:40: **CORRECTION to the ~18:30 entry (JYH
  refinement): the post-sprint local-zero-density item is a
  DECISION POINT, not a ratified arc** — "revisit ... and decide
  whether to unpark it." At sprint close the house brings JYH the
  unparking decision with: the Rb-4 obstruction statement, a
  design-arc scope estimate (the Riemann–von Mangoldt → gated
  C-nodes decomposition, SW-arc pattern), what it buys (the wall
  unconditional; zero-density technology; the N1 |ζ| ≤ C log T
  reusable), and the competing queue (Night Cycle, release lane,
  writeup drafting). No commitment implied before that review.

- 2026-07-15 ~18:50: **G-PIUPPER-FIX COMPLETE + the house consumer
  retype — the op-satisfiability tension RESOLVED end-to-end** (fix
  ≈ 129k tokens / 25 tools / ~16 min). The keystone's hypothesis is
  now `hlogNz : log N ≤ 3·log y + log z` — hND_le_ly reproved SHARP
  via the pairSet' bounds q₁ ≥ z, q₂ > y (logND = log N − log q₁ −
  log q₂); satisfiability at op verified with margin ≈ (1/8)·log N
  (the old form failed by 3·N^{−1/3}; the new form's z-term
  dominates precisely the blocker). The executor STOP-AND-FLAGGED
  the consumer breakage exactly as anticipated (Lean's exact-match
  on hypothesis types — no PiUpper-only formulation avoids it);
  the house landed the paired two-line retype in CountFinal.lean
  (hlogNy → hlogNz at both theorems + the docstring resolution
  note). Full build exit 0 (8967 jobs) — **the count chain is now
  op-instantiable; the G-OP path is clear.** Fix economics: catch
  248k + fix 129k + house edit ≈ one node's budget for a tear that
  would have been vacuous-at-op if consumed blind.

- 2026-07-15 ~19:10: **Q6b-GATE: GO_W_CORRECTIONS — THE GATE CATCHES
  THE DESIGNER: the frozen main term was CLASSICALLY FALSE** (cost ≈
  81k tokens / 13 tools / ~7 min — the sprint's cheapest gate and
  arguably its most valuable). C1 (BLOCKING): the design's main term
  𝔖·x/(log x)² pattern-matched the UNWEIGHTED twin count — but
  p1PrimeSum carries the Λ-weight (verified against the landed
  p1_carrier_inhabited witness: the n = 17 term IS log 17), so the
  true order is C₂·x/log x (the window halves 𝔖 to C₂) and
  TwinTypeII as frozen was FALSE for every A > 1 — while the
  implication would still have COMPILED (a valid derivation from a
  false premise; the build-invisible genre). C2: mathlib's tprod
  junk-defaults to 1 without a Multipliable witness — the positivity
  obligation would have passed ON A LIE (0 < 2); the design's own
  c₀-undershoot dodge REFUTED (a two-sided asymptotic needs the
  exact constant); the genuine Euler-product chain priced C-tier.
  C3: wall_or_door carries the full hypothesis set. C4: θ was a dead
  binder. PASSED CLEAN: the dichotomy contraposition (quantifier
  match verified at Wall.lean:533), the survivor re-point
  (CONFIRMED EASIER than P₂ — keepR 1 filters to primes, no
  prime-power crumb), import hygiene (TwinDeficit + Wall reach
  everything, no capstone drag). All four corrections applied to
  q6b-design.md; Q6b-DOOR dispatched (~300k, the twinC2 sub-node
  STOP-AND-FLAG-able alone). NINTH design-layer catch of the
  sprint; the first against the HOUSE's own freeze — the
  catch-the-designer datum the method paper needs.

- 2026-07-15 ~19:15: **G-SW2 COMPLETE — first attempt; the annulus
  absorption arithmetic kernel-certified** (cost ≈ 294k tokens / 49
  tools / ~28 min vs 350k). Salt/Goldbach/SW2.lean (514 lines):
  gold_hBlockW_of_window_prices, **gold_hNum_at_opW** (the annulus
  keystone: every price carries EXACTLY ONE range(⌊log₂N⌋+1) axis —
  24 occurrences, never nested; the A+1 absorption factor ≤ 1/log 2
  + o(1) < 2), gold_PloW_sym/low, the honest band triangle
  (pre-built for G-PDIAG, de-risking it), and the p₃-piece/m-split
  decomposition layer (Parts B/C — a SCOPE SURPRISE: the Goldbach
  world lacked the block↔box connective tissue; ~180 lines new).
  Correct deviation: the CRUDE diagonal path not built (the honest
  terminal routes through the residue crumb — catch #68's lesson
  encoded). Ceremony: wired + 8 keystones — full build exit 0
  (8968 jobs). **G-PDIAG DISPATCHED (the Chen-2 terminal-discharge
  node) ∥ Q6b-DOOR DISPATCHED.**

- 2026-07-15 ~19:45: **Q6b-DOOR COMPLETE — THE SPRINT SLATE CLOSES:
  ALL SIX REGISTERED QUESTIONS HAVE FINAL OUTCOMES** (cost ≈ 182k
  tokens / 49 tools / ~19 min vs 300k; one serious pass, 3 name
  fixes). Salt/TwinBar/TwinDoor.lean (295 lines): **twinC2 with the
  GENUINE Multipliable witness** (summability via the (p−1)² ≥ p²/4
  comparison → Real.multipliable_of_summable_log; twinC2_pos EARNED
  via exp(Σlog) > 0, not the junk default — the C-tier sub-node
  landed, no flag); TwinTypeII/TwinB_min at the gate-corrected
  Λ-weighted main term; **twinB_min_implies_twins :
  TwinB_min → TwinPrimeConjecture** (the door: A = 2 domination +
  the survivor extraction, confirmed easier than P₂);
  **wall_or_door** — the dichotomy, a one-line contraposition whose
  quantifier structure matched byte-for-byte on first write (the
  gate's verification paying off): every lower-bound certificate
  capturing a positive proportion of the prime-detecting instance
  is NOT SieveAgree-tolerant. R4 never tripped. One necessary
  deviation (adjudicated, accepted): import Salt.Basic added — the
  gate's import-hygiene check verified the sieve/wall vocabulary
  but overlooked the conclusion type itself (TwinPrimeConjecture
  lives in Salt.Basic, imported by NOTHING in the closure — a
  miss-genre worth the taxonomy: the gate checked reachability of
  the PREMISES, not the TARGET). Ceremony: wired + 6 keystones —
  full build exit 0 (8969 jobs). **Q6 FINAL: (a) the wall — landed,
  MmuRate-conditional budget, unconditional core; (b) the door —
  TwinB_min stated, the implication PROVEN, the dichotomy landed;
  the D-gap (proving TwinB_min = the P₁ lower sieve) is the
  corpus's precisely-stated open problem = flagship Challenge 2 +
  board entry #2. THE REGISTERED SLATE: Q1 mid-execution
  (checkpoint-ratified extension), Q2 ✓ Q3 ✓ Q4 ✓ Q5 ✓ Q6a ✓
  Q6b ✓.**

- 2026-07-15 ~20:10: **G-PDIAG COMPLETE — THE TERMINAL DISCHARGE
  LANDS; the band-chain re-cut closes ALL-FIRST-ATTEMPT** (cost ≈
  235k tokens / 33 tools / ~22 min vs 350k).
  Salt/Goldbach/PDiag.lean (623 lines):
  **gold_hBVblocksW_discharge'** (the terminal — Σ_j rosserRemainder
  ≤ N/(log N)^10 with the diagonal entering as the HONEST Pdiag row,
  catch #68's crude path correctly dead); gold_diagAggW_le_honest
  (the residue leg SIMPLER than the twin's — Band.lean's crumb
  bundles the two-step); gold_PloW_honest; the diagonal-support
  y·√N cards. The A+1 margin as assembled: the honest diagonal row
  is N^{5/6+o(1)} vs the N/(log N)^10 budget — N^{1/6} of room; the
  annulus log absorbed. BYTE-LOCKS for G-OP/G-ASM: the box Price
  carries FOUR indices (the annulus axis added — Opt-A's signature
  in the interface); hNX : N/2 ≤ X replaces hxX; the survivor
  prices/op rows/op point all hypothesis-parametrized and listed;
  the block-remainder → A₃ example DEFERRED to G-OP (only
  gold_mainA3_of_hBVswitch exists — the terminal exposes its exact
  slot). THE RE-CUT LEDGER: G-BAND flagged 187k → WindowSW 285k +
  BandIdent 308k + SW2 294k + PDiag 235k = 1309k for what was
  budgeted 380k as one node pre-flag — the honest coefficient
  (the twin's band chain ~3.3k lines re-derived at the reflected
  window), ~4× multiplier on THIS chain, all first-attempt under
  the re-cut. Ceremony: wired + 5 keystones — full build exit 0
  (8970 jobs). **G-OP DISPATCHED (the penultimate node).**

- 2026-07-15 ~20:40: **SPRINT 2 DIRECTION RATIFIED (JYH: "yes, this
  sounds good")** — ~3 days of research budget after sprint 1
  closes, two tracks, pre-registered under the sprint-1 protocol:
  **TRACK A (depth on known-hard, ~1.5 days): the N(T)/local-zero-
  density arc** — Riemann–von Mangoldt decomposed into gated C-nodes
  (the SW-arc pattern), targeting the Rb-4-named keystones (the
  argument-principle count, the one-power ζ′/ζ segment bound,
  N1 = |ζ| ≤ C log T); trophy: MmuRate discharges ⟹ THE PARITY WALL
  GOES UNCONDITIONAL + zero-density technology unlocked. This IS
  the unparking decision, resolved into the sprint. **TRACK B (the
  frontier, insight-shaped deliverables, ~1.5 days):** (1) the
  weight no-go atlas — the class-maximal P₁-invisibility theorem
  over the decoration-readable weights (extending heavy_semiprime_
  obstruction + deficit_floor; the switch-side M_k-atlas analogue;
  the flagship bet); (2) the TwinB_min attack-surface map — the
  Q6a-4 recon pattern on the classical routes to the P₁ lower
  sieve, each ending corpus-reachable-or-named-obstruction; (3)
  the GEH_min door statement (the Q6b pattern at H₁ ≤ 6); (4) the
  log-Chowla formalization cost map (recon only). STRUCTURE: hard
  mid-sprint checkpoint (JYH rebalances between tracks); an
  emergent-lead slot with an amendment protocol (the sprint-1
  lesson: the dichotomy and the self-funding no-go were unregistered
  emergents). AVOID: unfinishable monuments, "attempt to prove
  <open X>" framings, constant-optimization grinds. Registration
  draft comes to JYH at sprint-1 close (chen_goldbach or its
  final flag).

- 2026-07-15 ~20:55: **G-OP COMPLETE — the op layer lands; ONE
  accounting gap surfaced and adjudicated** (cost ≈ 244k tokens /
  70 tools / ~30 min vs 400k; 1 serious attempt). Salt/Goldbach/
  Op.lean (419 lines, 30 decls): the op definitions + the punctured
  moduli facts; **gold_op_Zpow9** (G-DENS's discharge route,
  landed); **gold_op_residue** (the reflected witness at Squarefree
  opQ + Even N + opQ ≤ N — every G-RES byte-lock consumed);
  **gold_a12_hA1** (the A₁ op bundle — ZERO new threshold lemmas:
  z/y/D/Q are byte-shared with the twin, so the whole
  a12_level/close/opf_tower layer reused at x := N);
  **gold_op_count_rows** (the count seam at op — the hlogNz row
  SATISFIABLE with margin ≥ log N/8 ≥ 12: the G-COUNT-2 catch's fix
  verified in anger); gold_op_hCE. HOUSE CEREMONY FIX: the executor
  imported the house aggregator (cycle on wiring) — swapped for
  concrete imports, the known genre (fin8d's lesson recurring;
  briefs say Chen.All, should say ANY .All). **THE ACCOUNTING GAP
  (adjudicated): the twin's mainA2 slot consumes the omega-carrier
  decomposition (omegaPrimeSumW_decomp, hard-wired to n+2) — in
  the census as mirror work but ASSIGNED TO NO NODE. The razor's
  three-term ledger needs mainA2 (the switch-only reading would
  leave the A₂ cost undischarged) ⟹ G-OMEGA COMMISSIONED** (the
  omega mirror + goldA2W_hcoef + gold_a12_hBV_A2 + gold_a12_hA2).
  Also remaining, precisely flagged: the survivor-price discharge
  (the 4-index annulus pricing into PDiag's rows — G-OP2) and the
  count fold to the seam shape. Ceremony: wired + 9 keystones —
  full build exit 0 (8971 jobs). **G-OMEGA ∥ G-OP2 DISPATCHED; then
  G-ASM.**

- 2026-07-15 ~21:30: **G-OMEGA COMPLETE — the accounting gap closes,
  first attempt** (cost ≈ 256k tokens / 55 tools / ~29 min vs 300k).
  Salt/Goldbach/Omega.lean (527 lines): goldOmegaPrimeSum (the A₂
  omega carrier at the reflected value), goldOmegaPrimeSum_decomp
  (over the PUNCTURED window — forced by the per-prime Coprime p N
  split; sound because window primes exceed y, the new
  gold_op_Yhalf fact), goldA2W_hcoef (rfl-grade),
  gold_a12_hBV_A2, **gold_a12_hA2** (the A₂ op bundle — the
  chen_of_hypotheses_W mainA2 slot's exact Goldbach shape). TWO
  INTRINSIC BYTE-LOCKS FOR G-ASM: (1) **the residue is parametric
  a, NOT opA** — the A₂ mod-transfer needs Coprime opQ (N−a), which
  opA = opQ−1 does not satisfy; the gold_op_residue witness supplies
  both coprimalities and must feed A₁/A₂/A₃ UNIFORMLY — and
  gold_a12_hA1 is currently hardcoded to opA, so **G-ASM needs a
  general-a A₁ instance** (re-invoke the A₁ chain at the witness);
  (2) the punctured aggregation window. New helpers with no landed
  analogue: gold_factors_ge_z_of_sift, goldOpP_pfull, gold_op_Yhalf.
  Ceremony: wired + 7 keystones — full build exit 0 (8972 jobs).
  G-OP2 in flight; G-ASM's brief carries both byte-locks + the
  general-a A₁ requirement.

- 2026-07-15 ~22:15: **G-OP2: the count seam LANDS; the survivor
  prices STOP-AND-FLAGGED — one supplier node remains before G-ASM**
  (cost ≈ 451k tokens / 101 tools / ~62 min — the arc's heaviest
  run; ~8 of the build cycles spent on ONE mechanical hazard, see
  the memo). LANDED (Salt/Goldbach/Op2.lean, 293 lines):
  **gold_hcount_seam** — the count seam at op, byte-matching the
  twin's shape at x := N, SIMPLER than the twin (the unrestricted
  goldTripleSum over φ(opQ) needs NO equidistribution crumb);
  corr_le_at_op reused VERBATIM; the concrete budget goldSeamC with
  ec ≪ 0.01 inside the razor's 1/100. THE FLAG (deliverable 1,
  honest and precise): the twin's survivor-price bodies HARD-WIRE
  crtClassW across five files (FinA3/FinA3b/AggSum/PriceOne/
  PriceClose — verified FinA3.lean:227) and carry a single
  T-difference (no annulus axis); no Goldbach crtClassG box-price
  supplier exists; reproducing that + the Σ_k annulus budget in one
  file was correctly out of scope. **G-PRICE COMMISSIONED** (the
  crtClassG price suppliers + hSum/hNum at op, the annulus axis
  threaded; the mainA3/hBVswitch slot is the last open input to
  G-ASM). FRICTION MEMO (recorded for all future op-point nodes):
  the op context's rpow/floor/log/integral terms send
  context-scanning tactics into whnf heartbeat loops — the
  resolution pattern is set+clear_value to freeze atoms, clear the
  defining equations before arithmetic, and linarith only [...]
  with explicit certificates (nlinarith only does NOT exist).
  Ceremony: wired + 1 keystone — full build exit 0 (8973 jobs).

- 2026-07-15 ~22:50: **G-PRICE COMPLETE — the suppliers + scaffold
  land first-pass; TWO SEAMS remain + an honest re-estimate** (cost
  ≈ 231k tokens / 56 tools / ~25 min vs 450k; the friction memo
  AVOIDED the whnf hazard entirely — zero cycles lost).
  Salt/Goldbach/Price.lean (207) + PriceClose.lean (150):
  gold_crtClassG_coprime_of_mem (the one genuinely-Goldbach
  bookkeeping row); **gold_box_price_engine** (the box/sym/low
  price — medium_survivor_price_sqrtD applied DIRECTLY at the two
  annulus cutoffs; the twin's medium_box_price_at_op is NOT
  annulus-reusable, its D0-window is hard-tied to L ≈ log x);
  gold_tower_budget + gold_hNum_close_of_tower (x-generic twin
  lemmas, verbatim); gold_mainA3_at_op (the parametric composition
  scaffold, byte-locking G-ASM). HOUSE RE-ESTIMATE (the executor's
  "even the twin's mainA3_at_op is unproven" grep finding is
  name-level only — chen_headline IS proven, so the twin's actual
  A₃-at-op discharge lives in the endgame's FIN-A3/FinLed chain
  under other names): **the remaining Chen-2 critical path is the
  two seams — (1) the per-annulus row discharge (the Goldbach
  AggSum/FinA3 analogue at the annulus axis) and (2) the
  block↔switch aggregation (gold_memClassG +
  goldBlockSwitchSieveW_abs_rem_le → the budget) — then G-ASM.
  These mirror the twin endgame's HEAVIEST stretch (the PRICE +
  FIN-A3 + HCOUNT waves ≈ 4M tokens there); with the suppliers
  landed and the engine generic, est. 2–4 nodes / 600k–1.2M here.
  Chen-2 is NOT two nodes from done; it is one seam-wave + G-ASM.**
  G-AGG dispatched (both seams, pre-authorized split; first task:
  trace the twin's ACTUAL hA3_bundle chain backward from Headline4).
  Ceremony: wired + 5 keystones — full build exit 0 (8975 jobs).

- 2026-07-15 ~23:30: **G-AGG COMPLETE — both seams' keystones land
  first-pass + THE ARCHITECTURAL CATCH: the twin's real A₃ route is
  the W/BLOCK path** (cost ≈ 274k tokens / 57 tools / ~25 min vs
  450k; the friction memo again cost ZERO cycles). THE TRACE (the
  brief's first task, delivered): the twin's hA3_bundle composes
  box/low/sym_price_indep → hSum_at_op → hCE/hRCE → hdiag →
  hNum_close → hBVblocksW_discharge' →
  **mainA3_of_block_remainders_W (SwitchW:340) — the W-route
  terminal, φ(Q)-normalized**. THE CATCH: gold_mainA3_of_hBVswitch/
  gold_mainA3_at_op carry the NON-W goldSwitchSieve with no /φ(Q) —
  the entire landed pricing chain (PDiag/SW2, all φ(Q)-normalized
  W/CRT objects) CANNOT feed them (the non-W sifted sum over-counts
  by φ(Q)); the Λ-bridge must target goldSwitchSieveW.siftedSum.
  G-AGG built the faithful W-route terminal instead of the brief's
  target — the correct deviation. LANDED: **gold_hSum_at_op**
  (seam 1's aggregate — the hSum slot character-for-character;
  RHD = (12·Ccon_box + 3·Ccon_band + Ccon_diag/2)·Kc·N/(log N)^11)
  + **gold_mainA3_of_block_remainders_W** (the composed A₃ terminal)
  + gold_log_absorb. The annulus axis enters at ^13/^12 → closes to
  ^11 (the A+1 saving, tower-dwarfed). FINAL G-ASM BYTE-LOCK
  recorded in Agg2 §3. THE ONE OPEN RESIDUAL: **gold_box_price_indep
  — the ~40-row analytic discharge at per-annulus geometry** (the
  twin's PriceOne mirror; the small-k vanish/live floor is the
  delicate part) — G-BOXROWS dispatched (the pilot's own 600k–1.2M
  wave estimate; pre-authorized split). Ceremony: wired + 3
  keystones — full build exit 0 (8977 jobs). Chen-2 critical path:
  G-BOXROWS (wave) → G-ASM.

- 2026-07-16 ~00:05: **G-BOXROWS: PARTIAL + THE EXACT BLOCKING ROW —
  the factor-8 window collision** (cost ≈ 189k tokens / 36 tools /
  ~17 min; 1 serious attempt at the hard part, then the flag per
  discipline). LANDED (Salt/Goldbach/BoxRows.lean, 260 lines, 5+
  keystones): the row inventory (41 rows classified a/b/c); the
  dead-annulus vanish pair (box_carrier_eq_zero_above_cap reused
  byte-for-byte); gold_box_XM_scale/XMhi (the annulus box geometry);
  the SW-coupling rows (verbatim at A=13/C0=18); two composition
  examples pinning the consumer slots. THE FLAG (exact): the twin's
  d0_window_of_XM has window (x/2, 4x] — factor 8 — and the annulus
  box range (goldCut k, 8·goldCut k] is ALSO factor 8; hXMhi forces
  x ≥ 2·goldCut k while hXMlo forces x < 2·goldCut k — NO single x
  admits both strict bounds; the T₁ clause is ONE UNIT short in the
  deep-live regime. RESOLUTION (a well-defined node, dispatched as
  G-D0WIN): d0_window_of_XM_annulus taking the un-incremented lower
  bound directly + the per-annulus live-box floor
  (goldCut(k+1))^{7/16}/8 ≤ 2^{k'} (the kfloor_of_live_box
  analogue); then the 14 box-geometry rows + the packagings
  (G-BOXROWS2). The pilot's wave forecast confirmed: the residual =
  G-D0WIN → G-BOXROWS2 → G-ASM. Ceremony: wired + 5 keystones —
  full build exit 0 (8978 jobs).

- 2026-07-16 ~00:40: **G-D0WIN COMPLETE — the off-by-one DISSOLVES:
  the strict bound was a packaging artifact, not a mathematical
  need** (cost ≈ 245k tokens / 28 tools / ~27 min vs 300k; every
  deliverable first-build). Salt/Goldbach/D0Win.lean (430 lines):
  **gold_d0_window_annulus** (the 9-conjunct window re-derived
  annulus-natively — the twin's hL_lo only ever used the NON-strict
  x/2+1 ≤ X·M; keyed to goldCut(k+1), reproducing the twin's
  L-window EXACTLY); **gold_kfloor_live_annulus** (the 7/16 live
  floor; the twin's x/2 cutoff becomes the full goldCut k, absorbing
  the factor 2); **gold_box_price_engine_at_live_annulus** (the
  composition — conclusion byte-identical to the engine's, dropping
  straight into the hprice slot). Every constant change documented
  (11/24 → 7/16 the only substantive one; all numeric closes
  re-verified). The executor also confirmed the collision was
  GENUINELY unsolvable via the twin lemma (the phantom-x set is
  empty; the X·M-keyed dodge fails the floor) — re-derivation was
  mandatory, and the flag chain (G-BOXROWS → G-D0WIN) was the
  correct decomposition. HEADS-UP for BoxRows2: the z-bound is
  annulus-LOCAL (holds on the top annuli where goldCut saturates);
  the live/dead dichotomy + slot mapping are in the handoff.
  Ceremony: wired + 3 keystones — full build exit 0 (8979 jobs).
  G-BOXROWS2 DISPATCHED (the packagings; then G-ASM).

- 2026-07-16 ~01:15: **G-BOXROWS2: STOP-AND-FLAG — the z-bound
  mismatch is STRUCTURAL; HOUSE ADJUDICATION: the z-dependent floor
  at the EXISTING threshold** (cost ≈ 227k tokens / 53 tools / ~28
  min; the DEAD half + interface pins landed —
  gold_box_price_row_dead, 115 lines; the executor correctly
  refused to discharge ~40 rows atop a false hypothesis). THE
  BLOCKER, exact: the Opt-A annulus decomposition made the box
  scales LOCAL (goldCut ≤ N/2) while z = opZ N ≈ N^{1/8} stays
  GLOBAL, and (opZ N)^8 > N/2 for N ≥ 2^40 — the landed
  kfloor/D0-window hz hypothesis is FALSE at op on EVERY annulus
  (the D0WIN handoff's "top annuli" belief refuted numerically;
  the /2 in the window top is exactly what breaks it). Live boxes
  provably exist, so vanish does not cover. Two design resolutions
  priced by the executor; **HOUSE ADJUDICATION (the arithmetic
  re-checked): resolution 2 — the z-DEPENDENT floor
  2^{k'} ≥ √(goldCut/(8z)) — and the executor's "larger op
  threshold" caveat is VACUOUS: the ratio needs goldCut ≥ (8z)^6,
  which live boxes (goldCut ≈ N^{19/24} vs (8z)^6 ≈ 8^6·N^{3/4})
  satisfy for N ≥ 2^{432} — and the LANDED tower threshold is
  exp(10^9) ≈ 2^{1.4×10^9}, astronomically above. NO
  operating-point change; option 1 (shrinking z) REJECTED — it
  re-opens the razor/switch balance and the certificate.**
  G-D0WIN2 dispatched: mirror D0Win at W_honest = ½·log(goldCut/
  (8z)) with the numeric conjuncts re-verified at the tower.
  Ceremony: wired + 1 keystone — full build exit 0 (8980 jobs).
  The remaining path: G-D0WIN2 → G-BOXROWS3 (the packagings) →
  G-ASM.

- 2026-07-16 ~01:50: **G-D0WIN2 COMPLETE, first attempt — the
  z-dependent floor lands; the structural mismatch is FIXED at the
  existing operating point** (cost ≈ 206k tokens / 34 tools / ~22
  min vs 350k). Salt/Goldbach/D0Win2.lean (528 lines):
  gold_live_annulus_lower (z·y² < 4·goldCut from pure live
  geometry); **gold_kfloor_live_z** (√(goldCut/(8z)) ≤ 2^{k'} — the
  false hz hypothesis is GONE, replaced by purely geometric
  conditions); **gold_d0_window_z** (the 9 conjuncts at W =
  ½(log goldCut − log 8z); the exp/floor bridge becomes an EXACT
  EQUALITY — cleaner than the landed e^7 ≥ 8 slack);
  **gold_box_price_engine_at_live_z** (conclusion byte-identical to
  the engine slot — the PDiag mapping unchanged).
  OP-SATISFIABILITY VERIFIED EXPLICITLY: the ratio hypothesis needs
  2·log y − 5·log z ≈ log N/24 ≥ ~29 — true from N ≥ ~2^{432};
  the landed tower threshold exp(10^9) dominates with margin
  ≈ 4×10^7. The adjudication held exactly. Ceremony: wired + 4
  keystones — full build exit 0 (8981 jobs). G-BOXROWS3 dispatched
  (the packagings; then G-ASM).

- 2026-07-16 ~02:25: **G-BOXROWS3: the collapse + the hSum close
  land; the HONEST residual re-scoped — the annulus mismatch has
  ONE more layer** (cost ≈ 257k tokens / 51 tools / ~20 min).
  LANDED (Salt/Goldbach/BoxRows3.lean, 284 lines, first-try proofs):
  **gold_box_price_live_kerr** (the LIVE engine collapsed onto the
  twin's boxPriceKerr BY DEFEQ — the price constant is shared with
  the twin, verbatim); gold_box_price_dead_kerr (both dichotomy ends
  on the SAME closed price); **gold_hSum_discharged** (the hSum row
  of the terminal closes character-for-character). THE HONEST FLAG
  (the executor refused the false "nothing-else-remains" example):
  the ~17 annulus-SCALE analytic rows (hXsqrt/hDsq/habs/...) are
  NOT landed — the twin derives them from its global window; at
  per-annulus scale they need the LIVE-GEOMETRY derivation (the
  D0Win2 pattern: e.g. hXsqrt holds at live boxes because 2^i >
  zy/2 ⟹ X > z²y/2 ≈ N^{7/12}, √X ≫ (log XM)^16 — TRUE, just
  needs the honest route); plus the sym/low band-engine analogues
  (medium_box_price_at_op_band / middle_medium_box_price_at_y
  mirrors). HOUSE: the residual is CONVERGING (band chain → box
  rows → D0 window → floor → scale rows + band engines — each
  revealed residual smaller and more precisely scoped).
  **G-ROWSLIVE ∥ G-BANDENG dispatched (file-disjoint, both consume
  landed material only); then G-ASM.** Ceremony: wired + 3
  keystones — full build exit 0 (8982 jobs).

- 2026-07-16 ~02:55: **G-BANDENG COMPLETE, first pass — the sym/low
  legs close structurally; everything funnels through the single
  two-T price** (cost ≈ 142k tokens / 36 tools / ~13 min).
  Salt/Goldbach/BandEng.lean (250 lines, 6 theorems):
  gold_band_price_sym/low (the hdiffK pricers — the annulus
  telescope via norm_sub_le, NOT box_disc_three_way: the Goldbach
  band telescopes over the CUTOFF axis carrying the full carrier,
  the twin never needs this); gold_hdiffK_sym/low_discharge
  (kernel-typechecked INTO SW2's slots — byte-match verified, not
  asserted); gold_band_annulus_absorb (the ^13 → ^12 log absorb);
  gold_band_hsym_slot (gold_hSum_at_op's hsym/hlow inputs
  VERBATIM). The one open input: the two-T single price = the SAME
  live-geometry op work G-ROWSLIVE is doing for the box leg
  (deliberately not duplicated). CONVERGENCE: the entire remaining
  A₃ analytic content now funnels through G-ROWSLIVE's row bundle.
  Ceremony: wired + 6 keystones — full build exit 0 (8983 jobs).

- 2026-07-16 ~03:40: **G-ROWSLIVE COMPLETE — every residual analytic
  row discharged at live geometry; ONE interface caveat, resolved by
  house arithmetic** (cost ≈ 433k tokens / 95 tools / ~58 min — the
  arc's second-heaviest run; 727 lines, 10 theorems, all
  first-serious-attempt). Salt/Goldbach/RowsLive.lean:
  gold_op_scales (the op floor/log bundle), gold_box_zx_rows
  (hz1/hz_ratio/hx from the live lower bound — the N^{1/24} margin
  in Lean), gold_box_wge/Mfloor/Xfloor (the N-power floors), the
  local numeric engine (ChenRows1's private engine re-derived
  public), and **gold_box_rows_at_op** — the box-price leg
  arg-free-but-for the four carrier rows, collapsing onto
  boxPriceKerr. THE CAVEAT (honest, documented): hDge + hDscale
  jointly force a PER-ANNULUS level D ∈ [w, 2w], w ≈
  √(goldCut/8z); a single global D provably cannot serve all live
  boxes (top needs ≥ N^{21/48}; low-annulus caps are ≤ N^{19/48}).
  **HOUSE RESOLUTION (arithmetic worked and checked): the
  per-annulus Dset split** — annuli with goldCut ≥ N^{7/8}-grade
  afford the global level bilinearly (√(N/2) = N^{24/48} >
  N^{21/48}); smaller live annuli price d ≤ cap_k bilinearly and
  the tail (cap_k, D_global] TRIVIALLY: per-d ≤ XM/(Q·d) + M, the
  tail sum ≤ goldCut·log + D·M ≤ N^{7/8}·polylog + N^{41/48} ≪
  N/(log N)^11 — polynomial room. G-DSPLIT dispatched (the split +
  tail bound + the final hprice packaging); then G-ASM. Ceremony:
  wired + 6 keystones — full build exit 0 (8984 jobs).

- 2026-07-16 ~04:15: **G-DSPLIT: STOP-AND-FLAG WITH A KERNEL-CHECKED
  REFUTATION OF THE HOUSE ADJUDICATION — catch-the-house #2** (cost
  ≈ 228k tokens / 38 tools / ~26 min; recon-first, the split items
  correctly NOT built). THE CERTIFICATE
  (gold_dsplit_head_cap_below_conductor, landed, 186 lines): the
  ~03:40 adjudication's premise "top annuli need no tail" is FALSE —
  it conflated the head cap 2w ≈ N^{7/16} = N^{0.4375} with the BV
  conductor opD N ≈ N^{0.49991}; the top annulus (X·M ≈ 2N) carries
  a non-empty tail whose mass is ≈ N, not a crumb — no constant
  enlargement exists. THE REAL FIX (executor-identified,
  house-verified THIS time by re-walking the twin's own closure):
  gold_box_rows_at_op UNDER-EXPOSES the level — the engine admits
  the WIDE window D·L^15 ≤ √(X·M), and the TWIN closes at its
  conductor exactly this way (the ε = 9/10⁵ saving in opD eats the
  L^15: at the tower, N^{0.00009} = e^{90000} vs L^15 ≈ e^{311}).
  The wide-head re-derivation does NOT need to edit RowsLive — a
  new file supersedes (the D0Win → D0Win2 pattern), following the
  twin's wide derivations (the top annulus ≈ the twin's global
  scale). With the wide head, tail-carrying annuli have goldCut ≤
  N^{1−2ε}·polylog and the trivial tail absorbs at margin
  e^{180000} vs (log N)^11 ≈ e^{228}. **G-ROWSWIDE dispatched**
  (the wide-window rows + the split at cap_k = √(XM_k)/L^15 + the
  hprice packaging). LEDGER NOTE: two house adjudication errors in
  one arc (the "no re-certification"-adjacent omega gap was an
  accounting miss; this one a LEVEL-SCALE conflation) — both caught
  by executors running the satisfiability discipline against the
  house; the asymmetric-catch data the method paper needs.
  Ceremony: wired + 1 keystone — full build exit 0 (8985 jobs).

- 2026-07-16 ~05:00: **G-ROWSWIDE COMPLETE — the wide keystone
  lands; the DSplit certificate's obstruction RESOLVED** (cost ≈
  205k tokens / 44 tools / ~35 min; 1 serious attempt, 2 mechanical
  fixes). Salt/Goldbach/RowsWide.lean (524 lines):
  **gold_box_rows_wide** — the box-row bundle at the WIDE window
  w ≤ D, D·L¹⁸ ≤ √(X·M) (the binding exponent is L¹⁸ via herr_lev,
  NOT the prose's L¹⁵ — a spec refinement, the tower swallows the
  L³); on top-grade annuli D := opD N is admissible at margin
  e^{90000} ≫ e^{373}. Six D-upper rows re-derived (routes
  documented); the D-independent rows reused verbatim; constant
  delta NONE (the same boxPriceKerr/Kc — the RHD row absorbs
  unchanged). **STRUCTURALLY CONFIRMED: the tail never touches
  XM ≈ N under the wide head — the DSplit fatal case no longer
  exists**; the residual tail lives only on goldCut ≤
  N^{1−2ε}·polylog annuli with margin e^{180000} vs e^{228}.
  Honest handoff (deliverables 3–5 scoped, not rushed): the trivial
  per-d bound + the tail sum + gold_box_hprice_at_op + the
  worst-W absorb mirror (boxPriceKerr_worst_le at the annulus
  boundary) + the sym/low leg instantiation. **G-HPRICE dispatched
  — the LAST pricing node; then G-ASM.** Ceremony: wired + 1
  keystone — full build exit 0 (8986 jobs).

- 2026-07-16 ~06:00: **G-HPRICE: STOP-AND-FLAG — CATCH-THE-HOUSE #3:
  the count·max annulus re-absorption is structurally wrong** (cost
  ≈ 181k tokens / 33 tools / ~17 min; one deep-scoping attempt, NO
  file fabricated — the firm negative per iron rule 4). THE
  OBSTRUCTION (corroborated at source level): gold_hSum_at_op's
  box leg carries the annulus Σ_k and demands per-box /L^13; the
  only pricer (boxPriceKerr via gold_box_rows_wide) delivers
  ≥ 12·Kc·XM/L^12 — at top-annulus live boxes (XM ≈ N, provably
  live) that is Kc·N·L/L^13 ≫ any constant·N/L^13; the trivial
  bound is bigger still. The count·max absorb (BandEng's
  gold_band_annulus_absorb + Agg's hbk) cannot recover the log
  from a TOP-DOMINATED GEOMETRIC sum. The twin never faces this
  (no annulus axis — one global price at /L^12 → one piece-sum →
  /L^11). **HOUSE REDESIGN (the arithmetic re-derived twice
  pre-dispatch this time): the GEOMETRIC-SUM absorption** — the
  per-annulus price is honestly ≤ C·Kc·goldCut(k+1)/L^12 (Km_min's
  L/logN ≤ 3-ish at live boxes ⟹ the blowup is the constant 3^49,
  absorbed into Ccon_box; XM ≤ 4·goldCut(k+1)); Σ_k goldCut(k+1) ≤
  8N (min(2^{k+1}, N/2) geometric); the box aggregate lands at
  ≤ C·Kc·N/L^12 — a FULL LOG inside the /L^11 terminal budget;
  the low-annulus tails enter as a SEPARATE additive crumb
  (≤ N^{1−2ε}·polylog·log ≪ N/L^11 at e^{180000} vs e^{228}).
  The fix is a new hSum supplier with the SAME LHS conclusion
  (the terminal's hSum slot consumes the aggregate bound — the
  internal decomposition is free); no landed file re-opens.
  G-GEOSUM dispatched with the complete design + the derivation
  in the brief. LEDGER: three house catches in one arc — the
  executors' satisfiability discipline is auditing the DESIGNER
  at the same rate the gates audit the executors; the method
  paper's most important single data series.

- 2026-07-16 ~06:45: **G-GEOSUM COMPLETE — the geometric absorption
  lands in Lean exactly as adjudicated; the count·max flaw is
  superseded** (cost ≈ 225k tokens / 73 tools / ~25 min; every
  keystone first-build). GeoSum.lean (372) + GeoSum2.lean (139):
  gold_boxPriceKerr_geo (the per-annulus honest price at the
  annulus scale — kerr_ratio_term_le reused verbatim);
  gold_goldCut_geosum (Σ ≤ 8N); **gold_hSum_geo** — the superseding
  hSum supplier, LHS character-for-character the terminal's slot
  (kernel-confirmed by the byte-lock example gold_hSum_geo_slot),
  the box leg absorbed GEOMETRICALLY + the tail as a separate
  additive crumb; RHD = (48·Cgeo + Ctail + 3·Ccon_band +
  Ccon_diag/2)·Kc·N/(log N)^11 — feeding gold_hNum_close_of_tower;
  gold_boxPriceKerr_geoN (the outer bridge at cr ≈ 24/11, Cgeo ≈
  9.5×10^34 — astronomically inside the tower budget). THE
  RESIDUAL (one node, precisely scoped): the terminal op-plumbing —
  Price := boxPriceKerr + trivialTail, the hprice discharge
  (DEAD/LIVE-high/LIVE-low), gold_box_disc_trivial + the tail sum,
  the two live ratios at op, the carrier/Dset matching. G-OPPLUMB
  dispatched — then G-ASM. Ceremony: wired + 4 keystones — full
  build exit 0 (8988 jobs).

- 2026-07-16 ~07:30: **G-OPPLUMB COMPLETE — the slot-level closure:
  hprice AND hSum both fill the terminal verbatim on DEAD +
  LIVE-HIGH** (cost ≈ 222k tokens / 63 tools / ~26 min; 4 keystones
  first-pass). OpPlumb.lean (276 lines): gold_box_live_ratios (the
  op ratios, cr = 3 with 5/4 slack), gold_box_hbox_geoN (the hbox
  summand), gold_box_price_wide_or_dead (the per-box dichotomy
  engine), **gold_box_hprice_op** (the terminal's hprice slot
  CHARACTER-FOR-CHARACTER at the QImage). HOUSE CORRECTION to the
  executor's residual framing: its DSplit-flag citation for the
  LIVE-LOW tail is STALE — DSplit's smooth-divisor fear was the OLD
  top-annulus case (goldCut ≈ N), superseded by the wide head; the
  remaining tail annuli have goldCut ≤ N^{1−2ε}·polylog where the
  CRUDE harmonic bound over ALL d ≤ conductor suffices (goldCut·log
  ≤ N^{1−2ε}·polylog at e^{180000} margin; conductor·M ≤
  N^{1/2}·N^{7/16} = N^{15/16} ≪ N/L^11 — M ≤ √(2XM/z) at small
  annuli). No delicate divisor estimate needed. G-TAIL dispatched
  (the trivial bound + the tail + the piecewise Price + the FULL
  terminal instantiation); then G-ASM. Ceremony: wired + 4
  keystones — full build exit 0 (8989 jobs).

- 2026-07-16 ~08:15: **METHODS III.3″ CODIFIED (JYH-ratified):
  "witness the slots at the operating point, not just the
  carriers"** — the Chen-2 amendment to the witness ladder, from
  the methodology review with the user: the arc ran refinement in
  ARCHITECTURE (terminal-first, byte-locked slots) and in
  DETECTION (all three house catches = stuckness at the point of
  consumption), but analogy in DECOMPOSITION (the inventory
  forward-mapped the twin; every tear sat where the analogy was
  load-bearing and false), and the witness discipline stopped at
  carriers — the budget-slot shapes were never instantiated at op
  at freeze time (premise latency hours, not ~0). The new rule:
  every rate/budget-shaped slot freezes WITH a worst-case concrete
  instance evaluated numerically at the op point. Estimated
  counterfactual: the 2.3× overrun → ~1.5×. Effective immediately
  (G-TAIL's brief already carries its arithmetic pre-verified; the
  G-ASM gate will run the slot-witness check on the assembly
  bundle).

- 2026-07-16 ~09:00: **G-TAIL COMPLETE — the harmonic tail lands;
  the glue node is all that remains before G-ASM** (cost ≈ 314k
  tokens / 67 tools / ~37 min; every theorem first-pass under the
  III.3″-pre-verified arithmetic). Tail.lean (310) + Tail2.lean
  (132): **gold_box_disc_trivial** (C = 0 — the trivial AP bound
  2XY/d + 2Y by elementary counting, the R-unit fibre collapse via
  ZMod cancellation); **gold_box_tail_le** (the honest harmonic
  saving via mathlib's harmonic_floor_le_one_add_log);
  **gold_box_price_tail** — the LIVE-LOW plug whose LHS is
  BYTE-IDENTICAL to the terminal's hprice slot (a verbatim-goal
  example compiles). Btail = 2(2XM/Q·(1+log bound) + 2M·bound); the
  per-box margins landed. REMAINING (Tail2's precise lock): the
  3-way piecewise hbox glue (DEAD/LIVE-HIGH/LIVE-LOW — all three
  branch values landed), the htail annulus-sum close (the
  ¬hDwide ⟹ XM ≤ N^{1−2ε}L³⁶ derivation summed against the tower),
  and the slot wiring (band/CE/diag/Num all landed) →
  gold_hBVblocksW_at_op. G-GLUE dispatched — pure composition, all
  pieces byte-locked. Then G-ASM. Ceremony: wired + 4 keystones —
  full build exit 0 (8991 jobs).

- 2026-07-16 ~10:00: **G-GLUE: the hprice/hbox glue LANDS + CATCH-
  THE-HOUSE #4 — the tail's Term B disproven at the claimed bound**
  (cost ≈ 242k / 54 tools; Glue.lean 208 lines landed: goldPrice
  piecewise + gold_box_hprice_at (the 3-way split COMPILED, slot-
  verbatim) + gold_box_hbox_at). THE CATCH: the house's
  "M ≤ √(2XM/z)" was BACKWARDS — the live floors force M ≈
  4XM/(zy) ≈ N^{0.5357}; Term B = Σ M·bnd ≈ N^{1.03} per live-low
  box (also: the live-low deficit is N^{0.006} from opDlev, not the
  N^{2ε} the brief said — both house errors). **HOUSE FIX
  (III.3″-verified at the worst case): the MIN-SIDE COUNT** — the
  trivial AP bound counts over EITHER side of the bilinear pair;
  min(X,Y) ≤ √(XM) < opQ·bnd·L^18 on live-low ⟹ Term B ≤
  opQ·bnd²·L^18 ≈ N^{0.994}L^18 ≪ N/L^11 at e^{6·10^6} vs e^{228};
  Term A unchanged. Executor-tier (the p-side count is symmetric to
  Tail.lean's m-side; min² ≤ XY elementary). Band gap (2): NO
  live-low issue — the band rectangles are top-grade (X ≈ N/2),
  the wide window covers the conductor; the mirror is
  RowsWide-pattern. G-FINAL dispatched (the min fix + the band
  mirror + the terminal composition; pre-authorized split).
  Ceremony: wired + 2 keystones — full build exit 0 (8992 jobs).

- 2026-07-16 ~10:45: **G-FINAL — THE A₃ BOX LEGS CLOSE; the terminal
  skeleton compiled with the residual list KERNEL-VERIFIED** (cost ≈
  263k / 63 tools; item 1 first-build). Final.lean (372) + Final2
  (182): apDiscBilinCutoff_symm (the carrier symmetry — the p-side
  reuses the m-side VERBATIM, cleaner than briefed);
  gold_box_disc_trivial_min (catch #4's fix, rigorous);
  gold_box_tail_min; min_le_sqrt_mul; the min-form price/hprice/hbox
  slots; **gold_hBVblocksW_at_op** — the terminal with the box legs
  FILLED character-for-character, residuals named in the statement:
  the band engine (hpriceSym/hpriceLow/hsym/hlow — the twin's band
  pricer is sub-box-tied; the Goldbach band needs the RowsWide
  pattern at top-grade X ≈ N/2), the htail tower close, hCE/hNum/
  hdiag (suppliers landed), + the structural op rows. G-BANDPRICE
  dispatched (the band rows at top-grade + the htail close + the
  op-leg wiring); then G-ASM. Ceremony: wired + 9 keystones — full
  build exit 0 (8994 jobs).

- 2026-07-16 ~11:30: **G-BANDPRICE — THE FOUR BAND BINDERS DROP FROM
  THE TERMINAL; one analytic residual + the op specialization
  remain** (cost ≈ 413k / 92 tools / ~49 min; first-attempt
  throughout, the two hard cores flagged not forced). BandPrice.lean
  (281) + BandPrice2.lean (189): gold_band_geo_absorb (the Wband
  grade via the ≤3-survivor collapse), gold_band_hpriceSym/Low
  (UNCONDITIONAL), gold_band_hsym/hlow (modulo the per-survivor geo
  price), **gold_hBVblocksW_at_op_band** (the terminal with the four
  band binders DISCHARGED IN-LINE), gold_btail_slot_firing_le (the
  per-box tail reduction at the honest opDlev exponents). DESIGN
  FINDING (the executor corrected the brief BEFORE building wrong —
  the census discipline maturing): "price the full band width" was
  wrong (X·M ≈ N² blowup); the correct route is box_disc_three_way
  on the ANNULUS DIFFERENCE, collapsing to ≤3 dyadic-boundary
  survivors at cutoff-scale area ≤ 2N. Ccon_band = 24·Cgeo.
  REMAINING (named in the compiled terminal): hgeoSym/hgeoLow (the
  per-survivor geo price = the LANDED wide_or_dead pattern
  re-derived at the band carriers), the htail summation, the op-leg
  specialization (hCE/hNum/hdiag at concrete op values), the
  structural rows, hbridge. G-SURV dispatched; then G-ASM.
  Ceremony: wired + 8 keystones — full build exit 0 (8996 jobs).

- 2026-07-16 ~12:15: **G-SURV: STOP-AND-FLAG — the band carriers are
  HIGH-PASS; gold_box_rows_wide's liveness gate prices only the
  low-pass half** (cost ≈ 267k / 30 tools; conclusive shape
  analysis, no file — correct per iron rule 4). THE FINDING: band
  survivors sit at m > z·pieceN (support floors at
  MediumFloor:144/183), spanning (5/24)·log₂N dyadic scales ABOVE
  the box engine's hlive gate — live-but-unpriceable; the twin's
  band route is LIVENESS-FREE (medium_box_price_at_op_band via
  d0_window_of_XM_band from a piece floor, ChenFinal2:327; the
  Y-variant boxPriceKerrY at AssembleA3b:634). TWO construction
  nodes needed: (1) the liveness-free annulus band pricer (the
  d0_window_of_XM_band analog at X·M ≤ 4·goldCut(k+1) feeding the
  base gold_box_price_engine + the geo conversion); (2) the
  boxPriceKerrY Y-variant for the middle piece. HOUSE ADJUDICATION
  (the firing question, arithmetic checked): low-annulus band
  survivors DO fire and the crumb does NOT absorb into the pure geo
  form (Term A costs L^13 against it) ⟹ **route a band-tail slot**:
  node (1) also delivers gold_band_hsym/hlow TAIL VARIANTS (same
  conclusions, + Btail routed to the htail crumb) superseding
  BandPrice's pure forms — the established supersession pattern.
  G-BANDWIN ∥ G-KERRY dispatched (both from the twin templates);
  then G-SURV-2 (the composition), the op/htail wiring, G-ASM.

- 2026-07-16 ~13:00: **G-BANDWIN COMPLETE — the liveness-free band
  pricer lands END-TO-END, all first-attempt** (cost ≈ 354k / 57
  tools / ~27 min). BandWin.lean (464) + BandWin2.lean (318), 11
  keystones: gold_d0_window_band (the band-floor D0 window — merges
  the annulus-native scale facts with the twin's band numerics; NO
  liveness, no z; margin ≈ 3.7× on the binding row);
  gold_box_price_engine_at_band → gold_band_box_kerr →
  **gold_band_survsum_geoN** (the hgeoSym/hgeoLow per-survivor
  grade on WIDE survivors, byte-locked); the firing branch priced
  by the min-form tail (goldBandBtailSlot — no DEAD-cap branch: the
  high-pass band has none); **gold_band_hlow_tail/hsym_tail** (the
  terminal shapes + the crumb routed, superseding the pure forms).
  G-SURV-2 residuals (flagged, not blocked): the minimal-diff
  terminal variant threading the band crumb into htail; the sym
  max-collapse; the geoN ratios at high-pass op scales +
  low-annulus vanish; the crumb tower close (the per-box conversion
  landed at gold_btail_slot_firing_le). G-KERRY still in flight;
  G-SURV-2 dispatches when it lands. Ceremony: wired + 7 keystones
  — full build exit 0 (8998 jobs).

- 2026-07-16 ~13:45: **G-KERRY COMPLETE — the Y-variant chain lands
  first-pass; BOTH construction nodes done** (cost ≈ 362k / 63
  tools / ~39 min). KerrY.lean (783 lines): goldBoxPriceKerrY +
  gold_kerrY_engine (the middle-piece sym price via the max-collapse
  + the boundary transfer + gold_d0_window_z at Nb := opY N + the
  generic pricer at N := opY — the twin's middle_medium engine was
  UNUSABLE at the Goldbach scale, exp(10^10) + the off-by-one; the
  native route replaced it); the geo conversions (Cgeo_Y = the box
  constant; the firing crumb REUSES the box leg's carrier-agnostic
  goldBtailMin verbatim). NOTE for G-SURV-2: the kerrY engine
  carries hlive — it covers the STRADDLING boundary index; the
  high-pass sym indices at the middle piece route through BandWin's
  liveness-free engine with the Y-indicator reconciliation — the
  composition node's case-split is now: DEAD-cap / straddling-live
  (kerrY or box engines) / high-pass-wide (BandWin geo) / firing
  (the min crumb), per leg. G-SURV-2 DISPATCHED (the full survivor
  composition + the terminal band-crumb variant + the geoN ratios +
  the crumb tower close). Ceremony: wired + 3 keystones — full
  build exit 0 (8999 jobs).

- 2026-07-16 ~14:30: **G-SURV-2: the compositional core lands + two
  blocks — AND THE HOUSE REFUTES THE ITEM-2 BLOCK (the y-floor
  arithmetic)** (cost ≈ 171k / 31 tools; Surv.lean 284 lines, 7
  keystones: both legs' per-survivor discharges, the band firing
  conversion, the leg-level tail compositions). THE EXECUTOR'S
  BLOCKS: (item 2) the high-pass geoN ratio "provably fails" at
  kp as small as 2; (item 4) the band crumb has no aggregation
  home. **HOUSE ADJUDICATION on item 2 (the arithmetic worked, the
  III.3″ check the executor skipped): the ratio HOLDS on all
  GENUINE band survivors — the executor's kp ≈ 2 counterexample
  ignores the p-side y-FLOOR: the sym indicator is blockPrimeInd
  (max (opY N) (pieceN k')), so the p-support is > opY ⟹ pieces
  with 2^{kp+1} ≤ opY have EMPTY survivors (the vanish lemma, from
  the max-indicator support) ⟹ kp ≥ log₂(opY) − 1 ≈ (1/3)log₂N;
  and the corner clause (2^i·2^kp ≤ goldCut ≤ N/2) with the y-floor
  forces 2^i ≤ N/opY ≈ N^{2/3} ⟹ i ≤ (2/3)log₂N < 2.1·kp ≈
  0.7·log₂N — the 10/31 ratio holds with margin N^{0.03}.** The low
  leg's analogous floor: derive from its carrier (executor task).
  THE FIX DESIGN (G-BANDCLOSE, dispatched): (A) the band kp-floor/
  vanish lemmas (sym from the max-support; low from its carrier);
  (B) the high-pass ratios at the floored kp (replacing the
  liveness route); (C) the aggregation variant with the band-tail
  slot (the ~180-line gold_hSum_geo supersession — new file,
  established pattern); (D) the tower close for BOTH crumbs (the
  per-box conversions landed both legs; the O(L²) count × the
  geometric annulus sum against the tower). Ceremony: wired + 5
  keystones — full build exit 0 (9000 jobs).

- 2026-07-16 ~15:15: **G-BANDCLOSE — (A)+(B)+(C) land: the y-floor
  vanish (via the p₂-cap, cleaner than the max route), the
  liveness-free ratio at cr = 4 (the item-2 flag's refutation
  formalized: 21·kp ≥ 10·i + 20 from the corner + the floor, T ≥
  123 suffices vs the tower's 2·10⁹), and gold_hSum_geo_band (the
  aggregation with the band-tail slot)** (cost ≈ 240k / 69 tools;
  2 serious attempts, (D)+(5) flagged at the protocol boundary).
  RESIDUALS: #1 the band WIDE pricer's analytic side-conditions at
  op (gold_band_box_kerr's rows — the RowsLive pattern at the band
  floors, which are STRONGER than the box's, kp ≥ log₂(opY)−1);
  #2 (D) the tower close for both crumbs (the per-box conversions
  landed both legs); #3 (5) the terminal re-wire consuming
  (A)-(D). G-BANDROWS dispatched (#1 + #2); then G-CLOSE (#3 + the
  op legs) → G-ASM. Ceremony: wired + 7 keystones — full build
  exit 0 (9002 jobs).

- 2026-07-16 ~16:15: **G-BANDROWS — BOTH residuals land: the band
  rows at op (the y-floor routes, 8× more room than the box leg)
  AND the tower close with Ctail_total = 240** (cost ≈ 353k / 63
  tools; att. 1 + att. 2). BandRows.lean (518) + BandRows2.lean
  (404): **gold_band_wide_price_at_op** (the 39-hypothesis engine
  discharged per-survivor off the y-floor — LHS definitionally
  goldLowSurvSum, plugging straight into BandClose's hbox →
  Surv's hwide); **gold_crumb_tower_close** (the shared triple-sum
  engine at honest deficits N^{−88/10⁶} dominant; box htail = 96,
  band hbandtail = 144). NOTE: the tower RAISED to log N ≥ 3·10^10
  (the band hx row) — N₀ inflates within tower-grade, fine.
  G-CLOSE dispatched (the terminal re-wire: the low chain
  definitional; the sym max-collapse boundary argument; the
  opD/bnd scale rows; the aggregate feed) — the LAST node before
  G-ASM. Ceremony: wired + 5 keystones — full build exit 0
  (9004 jobs).

- 2026-07-16 ~17:10: **G-CLOSE — the LOW leg closes end-to-end; the
  SYM leg 2/3; the wall isolated to ONE named hypothesis** (cost ≈
  380k / 70 tools; all keystones first-attempt). Close.lean (239):
  gold_band_hlow_wide_at_op (FULL — definitional, no liveness) +
  the slot wire; gold_band_hsym_wide_at_op (VANISH + COLLAPSE
  inline; the MIDDLE piece exposed as hmid). ★ FLAG G-CLOSE-1: the
  middle-piece WIDE survivors on large annuli are PROVABLY NON-LIVE
  (2^i ≈ N^{2/3} > the liveness cap N^{11/24}) — KerrY's engine
  copied the twin's liveness hypothesis, which the high-pass band
  cannot supply (the twin's box leg is live; the same "sym
  single-k" subtlety flags.md ~L7243 resolved differently there).
  THE MISSING SUPPLIER, exactly: the Y-indicator engine at the
  Y-FLOOR geometry — gold_band_wide_price_at_op's row derivations
  (landed at blockPrimeInd (pieceN kp)) crossed with KerrY's
  Y-indicator handling (landed at liveness) — ~400 lines, both
  parents landed. G-KERRY2 dispatched; then the terminal wire (the
  recipe is WRITTEN in Close.lean's docstring) + G-ASM. Friction
  catches: the one-point boundary gap folded into hmid; the band
  D-floor is a genuinely separate exposed row. Ceremony: wired + 3
  keystones — full build exit 0 (9005 jobs).

- 2026-07-16 ~17:50: **THE FORK PLAN RATIFIED (JYH: "yes, proceed
  that way")** — the Zeno diagnosis: the executors land their
  briefs; the briefs (house-compressed byte-locks) keep being one
  supplier short because no single context holds the band case
  space (leg × piece × annulus × live/high-pass × wide/firing).
  THE PLAN: if G-KERRY2 lands clean → the terminal wire stays
  Opus (transcription) and **G-ASM runs as a FABLE FORK** (full
  session context, zero STEP-0, designer-tier adjudication
  in-loop) — the one integrative node (the Λ-bridge at the
  W-sieve, the general-a A₁, the structural rows, the ∀N wrapper);
  if G-KERRY2 flags → the fork takes over IMMEDIATELY (hmid + the
  wire + G-ASM as one continuous job). The Opus-only budget rule
  (2026-07-14, JYH) is explicitly overridden for this node by
  JYH's ratification; est. fork cost 2–4× an Opus node vs the
  5-times-paid flag-return cycle. Recorded pre-execution.

- 2026-07-16 ~18:40: **G-KERRY2 LANDS — hmid DISCHARGED byte-exact;
  EVERY analytic supplier of the A₃ chain is now in the corpus**
  (cost ≈ 405k / 77 tools / ~65 min; 1 serious attempt). KerrY2.lean
  (855 lines): gold_kerrY2_engine (the y-floor Y-indicator engine —
  the window swapped to gold_d0_window_band when the y-floor
  provably could not supply hz_ratio; the engine made PARAMETRIC in
  abstract y so KerrY's hlo-proofs carry verbatim), gold_kerrY2_geoN
  (cr = 4, the weakened middle floor absorbed at 4× margin),
  **gold_hmid_discharge** (byte-exact vs Close:138-148). THE TWO
  IN-FLIGHT CATCHES: (1) the one-point boundary (pieceM = 2·opY+1
  breaks M ≤ 2N) resolved by blockPrimeInd(2^k'−1) =
  blockPrimeInd(2^k') — a prime power is not prime, k' ≥ 3 from
  opY ≥ 6; (2) the firing-crumb scope read off the consumption
  chain (hmid carries hDwide ⟹ pure-geo, the crumb is upstream) —
  no flag needed. The Kc-max reconciliation for the sym slot noted
  (the standard terminal pattern). Ceremony: wired + 3 keystones —
  full build exit 0 (9006 jobs). **PER THE RATIFIED PLAN: G-ASM
  DISPATCHED AS A FABLE FORK** (full session context; the terminal
  wire per Close's recipe + the Λ-bridge at the W-sieve + the
  general-a A₁ + the structural rows + the ∀N wrapper →
  chen_goldbach).

- 2026-07-16 ~19:50: **THE G-ASM FORK REPORTS — chen_goldbach is now
  a machine-checked corollary of ONE named analytic bundle** (the
  ratified Fable fork; cost ≈ 343k / 125 tools / ~69 min; 6 files,
  1677 lines, ALL sorry-free/axiom-clean; full build green). LANDED:
  the sym slot rebuilt at the unified Kc (the packaged lemma's
  opaque constant was unusable — the fork resolved in-flight);
  **gold_hBVblocksW_at_op_closed** (the A₃ block-BV terminal FULLY
  discharged — all 12 op rows); the razor chain with **the puncture
  catch** (the twin's hPfull' is FALSE at goldOpP — fixed via the
  p∣N → p = n ≥ z escape, needing 2·opZ ≤ N, free at kept points);
  the Even-N corner (the Λ-bridge genuinely needs it — threaded);
  **goldbach_of_hypotheses_W**; the Λ-bridge at the W-switch;
  the three main-term bundles at the parametric residue;
  **chen_goldbach_of_ledger** — the frozen D0 statement (NEVER
  weakened) from the single hL bundle. THE RESIDUAL, exact: hL =
  the Goldbach F2 ledger (the twin's normalized_package/certs arc —
  FIN-LED-scale): the A₁ fchain cert at the PUNCTURED W-lower
  bounds, the A₂ grid cert at the punctured filter, the A₃ cert
  assembly, the 1/200 error bundle at op. The dimensionless certs
  are the SAME numbers (the X_W cancellation); the W-normalization
  plumbing at the punctured modulus is the new content. Est. 3–5
  nodes / 1–1.5M, or a second fork. **DECISION POINT → JYH (the
  chime): finish the ledger arc now, or ship Chen-2 as
  reduced-to-one-bundle (an honest publishable state) with the
  ledger as the first sprint-2 item.** Ceremony: wired + 10
  keystones — full build exit 0 (9012 jobs).

- 2026-07-16 ~20:55: ██ **CHEN_GOLDBACH IS KERNEL-CHECKED — SPRINT
  QUESTION Q1 CLOSES; ALL SEVEN OUTCOMES (SIX QUESTIONS + THE
  RATIFIED EXTENSION) ARE FINAL** ██ (the hL closing fork: ≈ 223k /
  109 tools / ~54 min; 919 lines across 4 files; the build-time
  audit: ✓ chen_goldbach [3 axioms], full build 9016 jobs).
  `chen_goldbach : ∃ N₀, ∀ N ≥ N₀, Even N → ∃ p q, N = p + q ∧
  p.Prime ∧ IsP2 2 q` — the frozen D0 statement BYTE-EXACT, never
  weakened through 40+ nodes. THE CLOSE: totalMass twin-identical
  by rfl (the singular-series cancellation, end to end); the A₂
  grid at the punctured filter by filter weakening; the punctured
  W-ratio through the landed folded form; the count seam with NO
  equidistribution crumb; normalized_package consumed UNCHANGED.
  THE ONE NEW MATHEMATICS: the punctured depth facts via a
  TEN-PRIME BERTRAND CHAIN (the twin's two-step argument cannot
  survive puncturing — nine chain primes dividing N forces
  N < N·N^{1/8}/2^{108}, contradiction) — the arc's final elegant
  move. MARGINS: the error bundle ≈ 0.00374 vs 1/200 budget,
  twin-identical; the puncture costs one factor 1+16/(z−2) ≈
  3.9·10⁻⁶ vs 10⁻⁵ headroom. THE ARC TOTALS: ~50 landings, ~15.5M
  executor tokens (≈5.3× the 2.9M estimate — the honest reuse
  number), 6 house catches + 1 house-refutes-executor, 2 Fable
  forks (the ratified Zeno fix — the closing fork discharged in
  ~54 min what projected as 3–5 briefed nodes), 0 wrong proofs,
  the build green at every one of ~45 ceremonies. Ceremony: wired
  + 7 keystones — full build exit 0 (9016 jobs). NEXT: the JYH
  checkpoint — the sprint-1 report, the sprint-2 registration
  sign-off, the writeup resumption.

- 2026-07-16 ~21:40 (SPRINT 2): **B4 COMPLETE — the log-Chowla
  distance map lands; the verdict: OFF THE CURRENT FORMALIZATION
  MAP** (cost ≈ 45k / 10 tools / 4 min — the cheapest deliverable
  of either sprint, and among the most quotable). THE MEASUREMENT:
  (1) the corpus's deep assets POINT THE WRONG WAY — Tao's proof
  and its MR input deliberately avoid zero-free regions, so the
  entire SW investment does not transfer; (2) the corpus's Liouville
  carriers are the WRONG AVERAGING (Cesàro vs logarithmic — and the
  difference is load-bearing: natural-averaged 2-point Chowla is
  still OPEN); (3) mathlib has NO discrete Shannon entropy — no
  H(X), H(X|Y), I(X;Y); it stops at negMulLog and klDiv — the
  entire information-theoretic chapter is unwritten; (4) the
  deepest gap: THE ENTROPY-DECREMENT HEART — bespoke to the 2016
  paper, no formalization at any granularity in any system, on a
  foundation that does not exist; co-deepest by volume:
  Matomäki–Radziwiłł (never formalized anywhere) + Halász (needs
  the absent pretentious-distance machinery). THE TOTAL: floor ≈
  90+ C-nodes / ≥22M tokens (3+ SW arcs), D-dominated, unbounded
  upper tail. The ONLY landed input: λ(pn) = −λ(n) (class A).
  The registered deliverable — the first cost map from a
  formalization corpus to the modern analytic frontier — is
  delivered; B4 CLOSES.

- 2026-07-16 ~22:10 (SPRINT 2): **B2 COMPLETE — the attack-surface
  map at terminal precision: FOUR routes, ZERO survive to a P₁
  partial-progress node; R4 held at deficit_floor_of_certs** (cost
  ≈ 153k / 20 tools / 6 min). (i) Chen's reversal: REFUTED — the
  decoration-readable form by heavy_semiprime_obstruction (landed);
  the bilinear pair-switch form obstructed by the deficit floor
  (the reversal's success inequality IS the negation of the landed
  razor deficit); pairE2_upper named. (ii) Harman alternation:
  CORPUS-REACHABLE node map (G1 = the upper keystone at the A₁
  carrier, B; G2 = the BV remainder, LANDED; G3 = the Fchain value
  at s ≈ 4, C-reuse — the [1,3] mass-ledger identity does NOT
  cover s = 4, a genuine new panel regime) — but the endpoint is
  THE SHARPER NO-GO (p1RazorValue ≤ −δ unconditional-on-U), never
  P₁; **the recon PRE-ARMED the Zeno tripwire on this chain per
  the registration clause — construction awaits JYH discussion.**
  (iii) the dispersion route: TWO named missing theorems (GAP-E =
  the E2 lower count, genuinely new analytic content, and even
  landing it externally completes the NO-GO not the door;
  TwinTypeII itself at θ > 1/2 = flagship Challenge 2). (iv)
  [census-added] the parity-blind Selberg/Rosser lower certificate:
  REFUTED by the landed wall (MmuRate-conditional — the Track-A
  dependency made explicit). The III.3″/case-space obligations for
  any follow-up recorded (the F(4) DDE evaluation + the s-regime
  enumeration). B2 CLOSES: the jackpot did not hit; the map is the
  deliverable, at exactly the registered precision.

- 2026-07-16 ~22:40 (SPRINT 2): **THE TRACK-A TERRAIN MAP LANDS —
  Rb-4's verdict-D may be a ROUTE ARTIFACT** (cost ≈ 157k / 19
  tools). THE FINDINGS: (1) A1 is ~70% LANDED — the disk-Jensen
  count (entire_zero_count_le + M0zeta + the 1/4 center bound) gives
  the box count at the correct log RATE (constant 45× loose at the
  III.3″ witness — acceptable); the missing pieces are the radius
  extension + the functional-equation fold, both C. (2) The
  argument-principle route is STRICTLY DOMINATED: mathlib has NO
  multi-pole argument principle (rectBI is single-pole), Backlund's
  argument-variation is D-tier — Jensen wins outright. (3) THE
  TROPHY RE-ROUTE: the classical |1/ζ| ≤ C·log comes from 3-4-1
  POINTWISE (landed!) + A2a, ZERO density consumed; the left
  transport is a SHORT segment (~1/log T) where even the landed
  two-power bound integrates to ONE power — Rb-4's rejection
  assumed a unit-length transport. THE FORK, isolated: T-1ζ (the
  uniformity of the lower bound on the full vertical contour) — C
  if uniform, D if the zero-avoiding contour's deformed sums need
  the scale-u density. DESIGN FROZEN (s2-trackA-design.md): wave 1
  = A1-ab + A1-c + A2a (safe under every outcome) DISPATCHED; the
  T-1ζ uniformity SUB-RECON dispatched (the recon-first clause);
  the trophy executor gated on its verdict.

- 2026-07-16 ~23:20 (SPRINT 2): **A1-ab LANDS first-attempt + THE
  FORK ADJUDICATES C-GO-VARIANT — the trophy is REACHABLE by the
  shallow contour** (A1-ab ≈ 181k; the fork recon ≈ 144k). A1-ab
  (Salt/SW/BoxCount.lean, 219 lines): zeta_box_divisor_le +
  zeta_box_count_half at C ≈ 209 — AND the t-split COLLAPSES (the
  corpus counts zeros of the entire (s−1)ζ, so the pole contributes
  divisor 0: uniform in t, no case space — a simplification the
  design didn't see). THE FORK VERDICT: (1) the DEEP contour is
  confirmed D — the landed c₃ = 1/50456 makes the transport
  t^{4·10⁶}-fatal; Rb-4 was right about THE ROUTE; (2) **the
  SHALLOW contour (Re = 1 − c₄/log⁹T) + ADDITIVE short transport
  (Titchmarsh 3.11: transport ζ itself, never log ζ — no
  exponentiation) delivers |1/ζ| ≤ C·log⁷T, POLY-LOG, ZERO density
  consumed** — numerically verified at t = 10⁶/10⁹/10¹² with
  positive margins; (3) the Perron budget closes at log T =
  (log x)^{1/10} → |M_μ(x)| ≤ C·x·exp(−c(log x)^{1/10}) —
  MmuRate OVER-delivered (sub-exponential); (4) the ONE load-bearing
  dependency: A2a must hold on σ ≥ 1 − c/log t (the strip — the
  running executor's brief already states this range); (5) the
  BC-Harnack deep variant shelf-noted for a future sharper rate.
  THE TROPHY RE-SPEC (amending the design): T-lo′ (the 3-4-1 anchor
  + Cauchy-ζ′ + additive transport, C) → T-1ζ′ (the shallow-contour
  poly-log, C) → T-Mμ (the budget, C). Rb-4's verdict-D on the
  TROPHY is now a recorded ROUTE ARTIFACT — catch-the-house (Rb-4's
  own analysis) by a deeper recon; the wall's discharge is in
  reach. T-lo′ dispatches when A2a lands. Ceremony: A1-ab wired +
  3 keystones — full build exit 0 (9017 jobs).

- 2026-07-16 ~23:55 (SPRINT 2): **A1-c LANDS first-attempt — the
  functional-equation fold WITH multiplicity preservation** (cost ≈
  185k / 37 tools). BoxFold.lean (260 lines): the COMPLETED
  functional equation as the engine (Λ(1−s) = Λ(s),
  hypothesis-free; the Gammaℝ factor's zeros all at Re ≤ 0 —
  outside the strip), the order transfer via analyticOrderAt_mul +
  the affine comp (deriv −1 ≠ 0); zeta_analyticOrderAt_one_sub +
  zeta_zero_one_sub_iff + the honest cos/Γ case enumeration
  (zeta_fe_factor_ne_zero — the cos zeros at the odd integers,
  outside (0,1)); **zeta_box_count_full** (parametric: 2C, no seam
  term — the [1/2,1) left-closure partitions exactly; the Im-flip
  free since |−t| = |t|). CEREMONY NOTE: the fold's hhalf/hfin are
  parametric — the BoxCount disk-divisor → zBoxCount box bridge is
  a small house-composition item (A1-BRIDGE, folded into the next
  wave's brief). A1 as registered is now TWO composable keystones
  from done. A2a still in flight; T-lo′ gates on it. Ceremony:
  wired + 4 keystones — full build exit 0 (9018 jobs).
