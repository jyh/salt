# The catch taxonomy — anatomy-paper §3 dataset

*Built by a read-only pass over `docs/blueprints/flags.md` (the full ledger,
start to end), 2026-07-15. One row per catch #1–#78. Categories per the
task spec; the pre-outline §1½/§3 three-way scheme (transcription /
estimate-vs-statement / elided-argument) and METHODS Part III map onto the
finer eight-way scheme used here. **True count = 78, matching the final
ledger tally.** Numbering caveats (early catches implicit; #54/#55 have no
dedicated tally line; #76 has no standalone header; #79 never occurs) are
documented in "Ledger inconsistencies" below.*

## Column legend

- **Category** (one primary): `transcription` · `estimate-vs-stmt` ·
  `interface-unsat` · `carrier-mismatch` · `binding` · `numeric` ·
  `design-local` · `other`.
- **Loc**: `local` (one node/wave) · `iface` (between subsystems).
- **Found**: `gate` · `STEP-0` (inventory/recon) · `exec` (executor
  in-flight) · `kernel` · `numeric` (numeric-check) · `designer` (driver
  review).
- **Phase**: `build` (component construction) · `integ` (assembly/glue).
  Integration set taken as the assembly-seam and glue catches by content:
  {#41, #49, #58, #59–#78}; everything else is build.
- **Repair**: `additive` · `stmt-warrant` · `in-node` · `re-freeze`.
- **Cost**: `trivial` · `one-node` · `wave` · `multi-day`.

---

## The table

| # | Defect (≤15 words) | Category | Loc | Found | Phase | Repair | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
| 1 | Per-u coprimality atom unsatisfiable for high-ω u; needs sum-level bound | binding | local | designer | build | re-freeze | one-node | Maynard fragility 1; per-tuple ∀ vs average |
| 2 | Budget split between main and omitted-mass terms mis-drawn | design-local | local | designer | build | re-freeze | one-node | Maynard fragility 2; least-documented of the six |
| 3 | Constant hA11≤1/4 unprovable (only ≤0.6); first-moment Markov wrong | design-local | local | designer | build | re-freeze | one-node | Maynard fragility 3; fix = Chebyshev (2nd moment). numeric surface |
| 4 | Colliding-pairs S2 bound had wrong RHS (off by B1²), vacuous | design-local | local | designer | build | re-freeze | one-node | Maynard fragility 4; absolute vs signed; dimensional |
| 5 | lemma53 absolute error term B-type, dominates main → useless | estimate-vs-stmt | local | designer | build | re-freeze | one-node | Maynard fragility 5; every error term must carry f0-weight |
| 6 | lemma53 constant exponential 2^k; needs O(k) tight cascade | numeric | local | designer | build | re-freeze | one-node | Maynard fragility 6 |
| 7 | Level-1/4 trap: V2 char-sum outputs evaluate to x^{3/2} | estimate-vs-stmt | iface | gate | build | re-freeze | wave | BV design-gate; monolithic vs per-dyadic-block |
| 8 | Missing max_{y≤x}: single-x discrepancy gives only x^{3/2} | binding | iface | gate | build | re-freeze | wave | BV; "haircut absorbs a sandwich" was false |
| 9 | char_LS_max cannot close Type II; bilinear structure essential | design-local | iface | gate | build | re-freeze | wave | BV; forced the bilinear LS + Pólya–Vinogradov nodes |
| 10 | LS-bil thin-block mechanism pays √(#blocks) power loss | design-local | local | gate | build | re-freeze | wave | BV; "mechanism, not statement" |
| 11 | V2a mass conflation: TypeI₂ support UV gives x^{23/20} | numeric | local | gate | build | re-freeze | one-node | BV; fix U=V=x^{1/10} |
| 12 | Max-form LS genuinely obstructed; struck from DAG | design-local | local | gate | build | re-freeze | one-node | BV; a simplification more than a defect |
| 13 | V2b free-Q claim false; needs Vaughan-boundary terms + conductor cutoff | estimate-vs-stmt | local | gate | build | re-freeze | one-node | BV; 7th design correction (ledger count ambiguous) |
| 14 | SW de-smoothing needs real monotone carrier; ψ is ℂ-valued/oscillating | carrier-mismatch | local | gate | build | re-freeze | wave | fix = orthogonality-first fold to real ψ₁ carrier |
| 15 | Fixed-depth Bonferroni tail swamps V(z); no fixed K for consumer | design-local | local | STEP-0 | build | re-freeze | one-node | P0 recon; route killed, block-truncated Brun frozen |
| 16 | Recon dropped e² in denominator; sketched window 2× too wide | transcription | local | STEP-0 | build | re-freeze | one-node | page-image transcribe-first caught it |
| 17 | Block predicate's "all-of-d" reading violates paper's divisor-closure rule | transcription | local | exec | build | re-freeze | one-node | P0 B0; executor refused false equivalence |
| 18 | Freeze omitted (2.16) W-ratio bound from hypothesis decomposition | transcription | local | exec | build | additive | one-node | P0 B3; decomposition error = statement error |
| 19 | (2.18) redefines Λ and O-free freeze dropped z-threshold | transcription | local | exec | build | re-freeze | one-node | P0 B3b; statements gain z-large hypothesis |
| 20 | Assembly margin 5× thinner: omitted switched term's ½c̄ | numeric | iface | STEP-0 | build | re-freeze | one-node | Chen recon; true M≈0.0212 vs implied 0.203 |
| 21 | ε=1/200 blows sieve-slack ledger 21×M; re-froze 1/10000 | numeric | local | gate | build | re-freeze | one-node | Chen gate; designer compression error |
| 22 | BJS hypothesis (4) false for twin g with ℚ=∅ | interface-unsat | iface | gate | build | re-freeze | one-node | Chen gate; needs ℚ={p<u₀}; two lenses independently |
| 23 | Blueprint mixed Tao switch-tuning with BJS remainder; margin negative | carrier-mismatch | iface | gate | build | re-freeze | one-node | Chen gate; two source conventions irreconcilable |
| 24 | Erratum in BJS v6: printed (14) sums over odd n | transcription | local | numeric | build | re-freeze | one-node | Chen gate; source's own misprint, not in errata |
| 25 | linear_sieve_lower hsupp unsatisfiable: side-2 sieve forces P p ∀prime | binding | local | exec | build | stmt-warrant | one-node | executor delivered divisor-restricted variants |
| 26 | EstermannPositivity false: hypotheses don't force r summable | transcription | local | exec | build | stmt-warrant | one-node | machine-checked counterexample; add abscissa hyp |
| 27 | σ-map forgets sub-sieve cutoff p; change-of-variables not statable | carrier-mismatch | iface | exec | build | re-freeze | one-node | "carriers must carry enough"; cutoff-threaded skeleton |
| 28 | StepHyp's bare ∀ ranges over points where comparison is false | binding | iface | exec | build | re-freeze | wave | windowed redesign; out-of-window points trivial (T=0) |
| 29 | hτrec's global n=0 demand impossible; recursion holds only n≥1 | binding | iface | exec | build | stmt-warrant | one-node | one-token ∀→∀n≥1 amendment |
| 30 | Designer's repair (carry fseq decay) unsound; τ stays parametric | design-local | local | exec | build | re-freeze | one-node | executor machine-checked counterexamples |
| 31 | A₁ interval [39/10,4] unreachable; target only at s=4 endpoint | numeric | local | exec | build | stmt-warrant | one-node | C0 Amendment 2; ε′=10⁻⁴ |
| 32 | StepHypWP undischargeable at ε-order; missing loBnd/parity structure | interface-unsat | iface | gate | build | re-freeze | wave | machine-checked counterexample; conditioned contract |
| 33 | E₁a stated only s≥2; odd-flat branch needs s∈[1,3] | transcription | local | gate | build | additive | one-node | source lens; new E₁a-flat lemma |
| 34 | upset_mass_le too loose at flat cell boundary; blows budget | numeric | local | exec | build | additive | one-node | window-relative mass bound at D'^{1/3} |
| 35 | massO integration limit off by one; drops support-edge mass | numeric | local | exec | build | in-node | one-node | ∫_3^{n+1} should be ∫_3^{n+2}; binds MR4 |
| 36 | MR2 flat coefficient wrong; dropped [1,2] slice of window | numeric | local | exec | build | in-node | one-node | 0.2126 → 0.35541 |
| 37 | MR2b's two tail-closure routes both numerically refuted | design-local | local | exec | build | re-freeze | wave | Φ super-linear; spawned MR2c/TK/SS re-architecture |
| 38 | MR2c super-profile does not self-propagate; Perron eigenvalue wall | design-local | local | gate | build | re-freeze | wave | route diverges 1.11/step; needs two-sided machinery |
| 39 | "34% margin" measured on wrong quantity; budget is head-precision razor | numeric | local | gate | build | re-freeze | wave | revised numeric-keystone architecture |
| 40 | Frozen hh/hf targets omitted ε-smallness; false for large ε | transcription | local | exec | build | stmt-warrant | one-node | both executors added hεsmall:ε≤1/1000 |
| 41 | A₃ C5 glue wrong by log x; count vs Λ-carrier scale mismatch | carrier-mismatch | iface | gate | integ | stmt-warrant | multi-day | THE deepest; H-amendment 1 + SW-A₃ wave; assembly-seam |
| 42 | Repair plan claimed switched-BV machinery landed; hPerE undischarged | other | iface | STEP-0 | build | re-freeze | one-node | scoping/inventory catch; hPerE = the research core |
| 43 | hPerE envelope 1/e² false; true decay 1/e (cancellation-free) | estimate-vs-stmt | iface | gate | build | stmt-warrant | wave | numerically decisive; reshape absorbed into A |
| 44 | four_term re-instantiation false; hDscale unavailable for most e | design-local | iface | gate | build | re-freeze | wave | "the discharge plan, not the statement"; PE3 v2 |
| 45 | Density split 4/φ(lcm) delivers 1/φe·1/φf term-by-term — false | design-local | iface | exec | build | additive | wave | φ(gcd) unbounded; needs δ-restricted LS (PE3c) |
| 46 | SS2 panel 39 fails by 1e-7 at 7-digit knots (rounding artifact) | numeric | local | exec | build | in-node | trivial | fixed with 8-digit sandwiches; not a real gap |
| 47 | Adjudicated C0 exponent 2(A+1) diverges at A=1; needs strictly more | estimate-vs-stmt | iface | gate | build | re-freeze | one-node | C0=A+5 frozen; level-deficit/D0 exponents coupled |
| 48 | No wholly-interior box; p₂≤p₃ ordering couples the sides | design-local | iface | exec | build | re-freeze | wave | two briefing corrections; (i) exact-geometry flavor |
| 49 | ×8 carrier normalization discrepancy; A₁-vs-A₃ razor negative; Mertens debt | carrier-mismatch | iface | gate | integ | re-freeze | multi-day | SW4 gate; the design's V(y) 8× below true; M-layer |
| 50 | hIdent under-powered; strip singleton wrong; pair-bijection missing | design-local | iface | exec | build | re-freeze | multi-day | 3 findings; folds with #49 → SW-fiber block |
| 51 | M4a false on subsequence; operating point at zero-margin window edge | interface-unsat | iface | exec | build | stmt-warrant | one-node | witness x=10^16; C0 Amendment 4 ε′=9/100000 |
| 52 | Cross-M asymmetry: cross-term treatment diverges for A>1 | design-local | iface | exec | build | additive | one-node | needs sub-poly divisor bound (DIV1) |
| 53 | Per-fiber-sieve diagnosis (of #49) wrong; count ~3.3× too loose | design-local | iface | designer | build | re-freeze | multi-day | page-level source; weighted count (CNT2) is the ×7 |
| 54 | Hyperbola window not tileable into O(log) rectangles; must live in carrier | carrier-mismatch | iface | STEP-0 | build | re-freeze | multi-day | spawned the WBV1–7 window-BV wave; no dedicated header |
| 55 | pairSet cutoff p₂≤√x vs sharp √(x/p₁); count overshoots c̄/2 by 3× | estimate-vs-stmt | local | exec | build | stmt-warrant | one-node | (187) tail is Θ(1/log x); no dedicated header/tally |
| 56 | Ordering band Θ(x/log)-thick; crude count overshoots by (log x)^{10} | estimate-vs-stmt | local | exec | build | re-freeze | one-node | fix = symmetry split (BND) |
| 57 | Band box not symmetric; hidden asymmetric α_low rectangle | carrier-mismatch | iface | exec | build | re-freeze | wave | frozen block×block model wrong; adds max(y,N) threshold |
| 58 | Value-cert gaps: A₂ aggregation 5.007× honest; docstring claim off 400× | numeric | iface | gate | integ | additive | one-node | end-to-end re-gate; FPC + A2W nodes |
| 59 | Nominal X·M window price is (X·M)/x-lossy; over-sums to x^{3/2} | estimate-vs-stmt | iface | exec | integ | re-freeze | wave | effective cutoff-mass ≪ X·M; m-sub-blocking (GBV2) |
| 60 | m-sub-blocking needs √x≤4X; medium band is short-m/long-prime | carrier-mismatch | iface | exec | integ | re-freeze | wave | BV extracts m-side; needs transposed/prime-side price |
| 61 | e-fold ErrSum does not transpose; needs dispersion (range empty) | design-local | iface | exec | integ | additive | one-node | adjudicated benign: m-floor z·y=x^{11/24} empties range |
| 62 | D<N hypothesis fails at operating point for band boxes | interface-unsat | iface | exec | integ | additive | one-node | honest kill needs only single-block-prime (GBV5) |
| 63 | Absorption tally per-modulus; crumb ×D over budget through characters | numeric | iface | exec | integ | in-node | trivial | fixed in-node: crumb vanishes when p∣condχ |
| 64 | D0 window empty at every boundary box; two rows jointly uninhabitable | interface-unsat | iface | STEP-0 | integ | stmt-warrant | wave | FIRST kernel-checked catch; root=stmt demands L^{C0} vs L^{A+2} |
| 65 | H-package torn: hPfull needs 2∣P, hPodd needs 2∤P (only P=0) | interface-unsat | iface | exec | integ | stmt-warrant | multi-day | kernel-checked; W-trick seam; H-amendment 2 + W-layer |
| 66 | h4 ∀-slot false for all K; supplier-internal, missed by STEP-0 | estimate-vs-stmt | iface | gate | integ | stmt-warrant | wave | H2-gate; conditioned slot H4C (31 rows) |
| 67 | Tower row Q≤e^{w₀} unprovable in-corpus (ineffective SW) | numeric | local | gate | integ | re-freeze | trivial | H2-gate; use Q≤4^{w₀} + tower |
| 68 | Diagonal budget aggregated over τ(Ps)×pieces; infeasible triple over-count | numeric | iface | STEP-0 | integ | additive | wave | kernel-checked; honest x^{5/6} close (PDIAG), 0 stmt changes |
| 69 | Per-e rows demand positivity of vanishing terms (e>X, ⌊X/e⌋=0) | estimate-vs-stmt | iface | gate | integ | stmt-warrant | one-node | PRICE-gate; missing e≤X guard; witness/consumer diverged |
| 70 | PRICE-3 k-floor mechanism wrong; boundary only upper-bounds 2^k | design-local | local | exec | integ | in-node | one-node | k=2 counterexample; three-way carrier trichotomy |
| 71 | Edge box in dyadicBoundary(pieceN)\(2^k); no landed lemma prices it | carrier-mismatch | iface | STEP-0 | integ | stmt-warrant | one-node | supplier/consumer index-set seam; corner-clause relaxation |
| 72 | Band-carrier k-floor doesn't transfer from box; strip live/unpriceable | carrier-mismatch | iface | exec | integ | additive | one-node | band D0-window at x^{1/3} floor (fin6); 7th pre-construction |
| 73 | Sym middle-k carrier (collapsed shape + blockPrimeInd y) unpriced | carrier-mismatch | iface | exec | integ | additive | one-node | adjudicated small; middle_k_price at N:=y |
| 74 | Aggregation constant 9 orders above gate (post-#72 floor c=1/3) | numeric | iface | exec | integ | in-node | trivial | survivable only because consumer built parametric |
| 75 | A2grid demands exact log Dtot=4·log z; no operating point hits it | interface-unsat | iface | exec | integ | additive | one-node | #64 genre; window-perturbed cert (A2WIN) |
| 76 | Count keystone's inner ∃K per-instance; fixed C impossible | binding | iface | exec | integ | in-node | one-node | HCOUNT-3 uniform-K rebuild; no standalone header ("76→77") |
| 77 | Box/sym/low price dischargers not arg-free; params before ∀x | binding | iface | STEP-0 | integ | additive | wave | thresholds/constants un-extractable; arg-free restatements |
| 78 | A2grid_window still demands exact log yR=(8/3)·log z at top | interface-unsat | iface | exec | integ | additive | one-node | #75's twin at the top; window-perturbation (FIN-LED-2) |

---

## Summary statistics

**Verified total: 78 catches, 0 proofs on wrong statements** — the final
ledger tally is reproduced exactly. No number is doubled; #76 and #79 are
addressed under "Ledger inconsistencies."

### Category distribution (primary)

| Category | Count | % |
|---|---|---|
| design-local | 18 | 23% |
| numeric | 15 | 19% |
| carrier-mismatch | 11 | 14% |
| estimate-vs-stmt | 10 | 13% |
| transcription | 8 | 10% |
| interface-unsat | 8 | 10% |
| binding | 7 | 9% |
| other | 1 | 1% |
| **total** | **78** | |

The three "interface-shaped" categories (carrier-mismatch + interface-unsat +
binding) total **26 (33%)**; the three "estimate/statement" categories
(estimate-vs-stmt + transcription + numeric) total **33 (42%)**; pure
mechanism errors (design-local) are **18 (23%)**. The single `other` is #42
(a scoping/inventory catch: a repair plan that claimed an undischarged
hypothesis was landed).

### The headline claim: local vs interface, by phase

| Phase | local | iface | total | iface % |
|---|---|---|---|---|
| build (#1–40, 42–48, 50–57) | 33 | 22 | 55 | 40% |
| integration (#41, 49, 58, 59–78) | 2 | 21 | 23 | 91% |

**The claim holds, strongly for integration and directionally for build.**
Integration-phase catches are overwhelmingly interface defects (91%; the only
two local ones are #67, an in-corpus bound-availability fix, and #70, an
in-node mechanism correction). Build-phase catches are majority-local (60%),
but the interface minority is substantial (40%) — and it is not noise: it
concentrates in the two sub-arcs that were themselves multi-subsystem
integrations, the **BV rung** (#7–#9 interface) and the **switch-BV / PE /
count construction** (#22, #23, #27–#29, #32, #42–#54, #57 interface). This
refines the narrative: "interface defects live in the integration phase" is
true, but interface defects also appear wherever two subsystems meet, and the
BV rung was a small integration exercise embedded in the build phase (METHODS
III.1 already frames BV as "two systems, seven catches"). If the BV rung and
the switch-BV construction are re-read as local integration episodes, the
build phase's remaining catches are ~80% local — i.e. the phase↔locality
correlation is even sharper than the raw table shows.

### Discovery mechanism

| Mechanism | Count | % |
|---|---|---|
| executor (in-flight) | 37 | 47% |
| gate (adversarial) | 24 | 31% |
| STEP-0 inventory / recon | 9 | 12% |
| designer (driver review) | 7 | 9% |
| numeric-check | 1 | 1% |
| kernel (build/typecheck failure) | 0 | 0% |
| **total** | **78** | |

**No catch was surfaced by a raw build/typecheck failure** — the entire point
of the method. Five catches carry a machine-checked counterexample kernel
(#26, #32, #64, #65, #68), but each was *surfaced* by an executor, gate, or
STEP-0 inventory and then *confirmed* by the kernel; none was found by the
kernel rejecting a wrong proof. Adversarial gates + STEP-0 inventories
(the pre-dispatch mechanisms) account for **33 catches (42%)**; executors
holding the STOP-AND-FLAG line account for the plurality (47%). The seven
designer catches are all early (the Maynard driver-findings #1–#6 and the
page-level source diagnosis #53).

**Trend over time (pre-proof share).** Splitting into quartiles by catch
number, the gate+STEP-0 ("pre-any-proof") share is: #1–20 → 11/20 (55%, the
gate-heavy BV rung); #21–40 → 7/20 (35%); #41–58 → 8/18 (44%); **#59–78 →
7/20 (35%)**. So the *raw* pre-proof rate does **not** rise monotonically —
the BV design-gate era was already very pre-proof. The real integration-phase
trend is narrower and sharper: **terminal-node catches were caught before any
proof was attempted.** The ledger documents a run of six consecutive
"pre-construction / terminal-adjacent" catches (#64, #66, #67, #68, #69, #71)
and states "4 of 4 terminal-node catches pre-construction" at the end.
Moreover the integration-phase *executor* catches were themselves
STOP-AND-FLAG assessments during floor-A recon (e.g. #59, #60, #61, #72, #73),
i.e. before completing the node — so the "0 wrong proofs" invariant held with
margin across all 20 endgame catches, even though only 7 were pure
gate/STEP-0.

### Repair type and cost

| Repair type | Count | | Cost | Count |
|---|---|---|---|---|
| re-freeze (design change pre-exec) | 43 | | trivial | 4 |
| additive (new lemmas only) | 14 | | one-node | 47 |
| stmt-warrant (landed stmt edited) | 14 | | wave | 21 |
| in-node (fixed by discoverer) | 7 | | multi-day | 6 |

**No catch required demolishing landed work** (METHODS III.5's claim — of the
20 endgame catches, none forced a demolition). The 14 statement-warrant
repairs are all designer-tier edits under explicit warrant (H-amendments,
C0 amendments, hypothesis weakenings/additions); the 43 re-freezes are
design changes folded before dispatch (the dominant mode, because most
catches were pre-execution). The 6 multi-day repairs are exactly the
assembly-seam catches that spawned whole waves: #41 (SW-A₃), #49 (carrier
reconciliation + M-layer), #50 (SW-fiber → count + WBV), #53 (weighted-count
line), #54 (WBV window-BV wave), #65 (the W-trick layer). The cost
distribution is heavily one-node (47/78, 60%), confirming that individual
catches were cheap; the expense lived in the six that reshaped an arc.

### Patterns the narrative under-states

1. **`design-local` and `numeric` are the two biggest buckets (42% together),
   yet the paper's thesis is built on the interface categories.** Most catches
   were ordinary mechanism/constant errors caught at construction — honest but
   unremarkable. The *interesting* claim rests on the 26 interface-shaped
   catches, and specifically on the ~10 that were jointly-uninhabitable or
   carrier-mismatched at a seam (the ones reading cannot detect). The dataset
   supports the thesis but only after this filtering — worth saying explicitly.

2. **`carrier-mismatch` (11) is larger than `interface-unsat` (8) or
   `binding` (7), and it is the signature of the integration phase.** Seven of
   the eleven are integration-phase (#41, #49, #54?, #60, #71, #72, #73; plus
   build-phase #14, #23, #27, #57). "Two subsystems provably about different
   objects at the seam" is the modal integration failure — more common than the
   celebrated empty-window (#64) genre. The anatomy paper's case studies
   over-index on interface-unsat (#64/#65); carrier-mismatch deserves a study.

3. **The four "exact-geometry idealization" catches form a tight family**
   (#51, #64, #75, #78) — all "an idealized identity/window the operating point
   cannot hit," all late, all repaired by the same window-perturbation move.
   The ledger itself names them "#64 genre." This is a reusable failure-pattern
   the paper could name as a unit.

4. **Premise latency is visible in the data.** The catches with the longest
   gap between freeze and first instantiation (#64, #65, #66, #77) are all
   integration-phase, all binding/interface-unsat, all "supplier-internal"
   (the defect lived in a hypothesis threaded through many suppliers and never
   instantiated until assembly). This is METHODS III.2's central metric,
   observable directly in the table.

5. **The BV rung is a build-phase preview of the integration phase.** Its
   seven design corrections (#7–#13) are interface-heavy and gate-caught, a
   miniature of the Chen endgame 30 catches earlier. The paper could use it as
   a "we saw this coming" data point rather than treating #59 as the first
   integration catch.

---

## Ledger inconsistencies and numbering caveats (report exactly)

1. **#1–#16 are not individually numbered in the ledger.** Explicit
   `CATCH #N` headers begin at #17 (P0 B0). #1–#16 were reconstructed from the
   running-tally lines. The tally reaches **14** at the SW de-smoothing catch
   (line 2643, "14 design errors caught at gates across 5 rungs"), **15** at
   the Bonferroni catch (line 2646), **16** at the e² transcription (line 2679).
   Working backward, the clean and only self-consistent decomposition is:
   **#1–#6 = the Maynard track's six enumerated "fragilities"** (the ledger
   lists them verbatim at line 1618: per-u coprimality, budget split, hA11≤1/4,
   colliding-pairs RHS, absolute-vs-relative lemma53, lemma53 constant 2^k),
   **#7–#13 = the BV rung's seven "design corrections"** (the completion note,
   line 2600, states the count "7 design corrections" but does **not** enumerate
   all seven — I map them to the six labeled level-breakers plus the V2b
   free-Q/Vaughan-boundary correction; the seventh is genuinely ambiguous and
   could instead be the largesieve→BV L8.4 Barban re-freeze), **#14 = SW
   de-smoothing, #15 = Bonferroni, #16 = e².** 6+7+1 = 14 matches the tally.
   *Caveat:* the ledger also records design catches in the Brun, largesieve,
   and twinbar rungs (Brun's strict-vs-nonstrict statement amendment;
   largesieve's "unprovable 7N" and "Field-only Gauss lemma"; the L8.4
   re-freeze) that are **not** counted in this running total — so "14 across 5
   rungs" is a curated subset, and the true number of pre-execution design
   catches in the first five rungs is higher than 14. The #1–#13 mapping should
   be read as "the ledger's canonical count," not a complete census.

2. **#54 and #55 have no dedicated tally line.** The tally jumps directly from
   **53** (line 5776) to **56** (line 6126) — there is no "54 catches" or
   "55 catches" line. #54 additionally has **no `CATCH #54` header**; it is only
   referenced retroactively ("the catch-#54 assembly," "THE CATCH #54/#56/#57
   REGION"). By content #54 = the finding that the hyperbola window cannot be
   tiled into O(log) rectangles and must live in the cutoff carrier (the
   WBV-wave-spawning catch); #55 = the AB3 "landed design gap" (pairSet cutoff
   p₂≤√x vs the sharp √(x/p₁) that c̄ requires), fixed at AB4 and referenced as
   "catch #55 fixed."

3. **#76 has no standalone entry.** The ledger explicitly says "no catch #76"
   at two landings (A2WIN line 7457, and the HCOUNT-3 header "two catch-#76-class
   design flaws resolved in-node," line 7485). The number is then absorbed by
   the **"76→77 catches"** notation at FIN-A3 (line 7552), which counts #76 (the
   HCOUNT-3 in-node design flaws — the per-instance ∃K uniform-K rebuild and the
   base-7 E_SW / no-cbar-CORR corrections) and #77 (the not-arg-free dischargers)
   together, landing the running count back on the true value. So #76 exists as
   a counted catch but was resolved in-node without its own header.

4. **Minor internal inconsistency inside METHODS.md** (not the ledger): III.4
   attributes "the uniform-K rebuild" to **#76**, while Part I's doctrine list
   attributes it to **#77 (HCOUNT-3's uniform-K rebuild)**. The flags ledger is
   unambiguous — the uniform-K rebuild is the HCOUNT-3 in-node flaw, i.e. **#76**
   — so III.4 is correct and the Part I parenthetical conflates #76/#77. Worth a
   one-word fix when the anatomy paper cites either.

5. **#79 never occurs.** "No catch #79" is stated four times across the final
   landings (FIN-LED, FIN-LED-2, FIN-A3c, FIN-LED-3), and the arc closes at
   "78 catches, 0 wrong proofs." The count is closed and correct.

6. **The pre-outline's "~69 catches" is stale, not wrong.** pre-outline.md §0/§1
   were written mid-endgame (2026-07-14) and cite ~69; the arc finished at 78 on
   2026-07-15. The taxonomy is built against the final 78.

### Classification calls flagged as genuinely ambiguous

- **#64, #69** sit across two categories. Both are grouped by pre-outline §1½
  with the "jointly uninhabitable" trio and by METHODS Part I with the
  estimate-vs-statement doctrine. Primary here: #64 = interface-unsat (its
  defining symptom is an *empty D0 window*; the estimate-vs-statement L^{C0}
  vs L^{A+2} divergence is its *root*, noted); #69 = estimate-vs-stmt (rows
  demand positivity of vanishing terms; the missing e≤X guard is a
  binding-structure root, noted). Either could flip if the paper prefers the
  §1½ grouping.
- **#65** is filed interface-unsat (jointly uninhabitable H-package, per §1½)
  though pre-outline §3 files it under "elided arguments (the W-trick seam)" —
  the same event, two lenses.
- **#68** is filed numeric (a triple over-count budget-aggregation) though it
  *manifests* as an infeasible budget row (interface-unsat flavor); pre-outline
  §3 calls it "the diagonal aggregation" elided argument.
- **#67, #74** are borderline numeric/design-local — both are constant/bound
  issues resolved by parametricity or an available weaker bound.
- **#26, #40** are filed transcription (a hypothesis implicit in the source —
  summability, ε-smallness — dropped in the precise freeze) rather than
  interface-unsat, because each is *satisfiable* once the dropped hypothesis is
  restored; the defect is a translation gap, not an uninhabitable package.

Where a forced single category would mislead, the Notes column and this
section carry the second reading; a `notes` entry was preferred over a wrong
primary throughout.
