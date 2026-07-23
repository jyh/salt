# THE TERMINAL ASSEMBLY FREEZE — S8's last design block

*Maestro design block, 2026-07-22 morning (JYH-ratified: lift-first, the
thm_A1′ boundary). Status: **REFUTER PASS COMPLETE — repairs applied,
marked ⟦R⟧, FROZEN** (4/4 verdicts ~08:15: HF-REF-A=HOLD [the H-1 fatal
+ the factor-2 hazard — both repaired below], HF-REF-B/ASM-REF/TERM-REF
= REPAIR-THEN-FIRE; JYH's unanchored read had accepted all parts — the
verify-posture law's finest hour, banked as culture). Inputs: THE LIFT MAP (pilot
2026-07-21 18:16 — the hypothesis census with verbatim binders), the
L11-EDGE handoff (the ASM 4-step wall), MULT-SHIU CLOSED (MS-EXIT =
the budget), K4-WIRE landed, W-DOM landed, HalaszFactor's dissolution
verdict. Three parts; Part 1 is lift-first per the ratified ordering.*

═══════════════════════════════════════════════════════════════════
## PART 1 — HFACTOR-IDENTITY (the S1′ representation assembly)
═══════════════════════════════════════════════════════════════════

GOAL: discharge `prop21_analog`'s `hfactor` (HalaszRepAsm:452-456):
`‖(1/2π)•∫ seamDirichlet(f, windowIndicator y (X/y), t₀)(c₀+it)·hatKernel‖
− prop21RHS g t₀ X h c₀ y η‖ ≤ E` with E = the MS-EXIT budget. The Lift
Map's verdict: the ERROR BUDGET is supplied (MS-EXIT); what remains is
the REPRESENTATION IDENTITY + THE BRIDGE. New file:
`Salt/MR/HalaszIdentity.lean` (single writer).

### The design insight (H-4's dissolution candidate)

The scoper priced the "multivariable-Perron/Fubini coefficient identity"
multi-thousand-line because GHS Lemma 2.1/2.2 uses SHARP Perron. But the
corpus's hat kernel is EXACT (K2′), and the corpus already owns
Dirichlet-PRODUCT machinery: `dpoly_pow` (LargeValueCount — powers of
Dirichlet polynomials as convolutions), the kconv apparatus
(RamareDpoly), `kernel_sum_swap` (SW/Kernel:254). The design: the
four-factor product 𝒮(s−α−β)·𝓛(s+β)·P(s−β)·P(s+β) at each (α,β) is a
single Dirichlet series with CONVOLVED coefficients (the four-fold
convolution with the α,β-shifts as coefficient weights n^{±α},n^{±β});
`hat_contour_rep` applied in REVERSE turns prop21RHS's inner t-integral
into the hat-smoothed sum of those convolved coefficients — the
coefficient identity becomes Finset convolution algebra (the landed
pattern family), NOT sharp-Perron analysis. Fubini between ∫_t and the
coefficient sums = `kernel_sum_swap`'s hypothesis shape (absolute
summability from the c₀ > 1 line + 1-boundedness — the
`summable_bounded_weight` gate, landed).

### ⟦R — THE H-1 FATAL, REPAIRED (HF-REF-A's kill, the pass's crown)⟧

The original H-1 claimed an EXACT identity between the f-dependent seam
and the g-only four-factor product — but `prop21_analog` encodes NO f↔g
relationship (concrete falsifier: f = δ), and ellLin drops prime-power
values. THE REPAIR (statement-design tier, maestro-ruled): the campaign's
intent "g is f's prime datum" is MADE FORMAL, and the identity is
APPROXIMATE with every gap accounted in E:

- **H-0** [NEW, C, 250, FIRST] `seam_carrier_audit`: derive the exact
  relation between seamCoeff f (windowIndicator y (X/y)) t₀ and the
  g-built carriers, starting from `fgJ_factorization` (HalaszSeam:284)
  and `smoothPart` (HalaszLambda:402). Deliverable: the STATEMENT of
  H-EXIT — either (route i) `prop21_unconditional` carrying the
  hypothesis f = ellLin g (the tools become exact; consumers
  instantiate at the linearized datum), or (route ii) f generic with
  the prime-power LINEARIZATION defect (GHS's Λ_f/log n term) bounded
  and added to E. The executor lands the audit and PROPOSES the
  statement; the maestro ratifies before H-EXIT is stated
  (statement-layer law). STOP on any surprise.
- The ladder below is REORDERED (HF-REF-A's H-2 verdict): the
  realignment (old H-3) now precedes the FTC (old H-2), so the collapse
  runs on the aligned GHS-(2.3) form (𝒮 fixed at s), never on
  prop21RHS's mixed arguments directly.

### The ladder (order fixed; ~2.3-3.1k ln total)

- **H-0** as above [C, 250].
- **H-1** [B/C, 400] `seam_centering` (was H-3): the n^{-it₀} centering
  c-o-v (the full-line t-translation — SOUND per HF-REF-A's twist
  verdict: seamDirichlet's twist at c₀+it equals the untwisted series
  at c₀+(t+t₀)i; `MeasureTheory.integral_comp_add_right`) + the
  c_{α,β} = c₀−α−β/2 realignment + the β→2β substitution.
  ⟦R — THE FACTOR-2 MANDATE (iron-rule-1 tier): GHS's own printed (2.1)
  is arguably off by a factor 2 from (2.4) (the β→2β Jacobian; immaterial
  to GHS's upper bound, MATERIAL to our two-sided hfactor). The executor
  MUST track the Jacobian explicitly through this stone. If the factor 2
  is confirmed, the frozen `prop21RHS` definition is defective: STOP,
  report the exact arithmetic, and the maestro amends prop21RHS (a
  landed-definition surgery) before anything downstream is stated. Do
  NOT absorb the factor into E.⟧
- **H-2** [C, 350] `seam_double_ftc` (was H-2, now on the ALIGNED form):
  the (α,β) collapse on the (2.3)-form with 𝒮 genuinely fixed at s —
  the β-leg via `largeSeries_ftc_double_beta` (LANDED witness), the
  α-leg via `shifted_dirichlet_ftc` with the 𝒮-prefactor pulled out
  ONLY where constant (the aligned form guarantees it); the windowSum
  truncation (full 𝓛′ vs finite P) is NOT collapsed here — it is
  routed to H-5's defect (the freeze's old exact/defect split is
  redrawn per HF-REF-A: the truncation is woven, and lives in H-5).
- **H-4** [C, 700, THE RISK STONE — SURVIVED THE LOAD TEST]
  `four_factor_hat_rep`: ⟦R (HF-REF-B): the finite×infinite step rides
  the LANDED `LSeries_convolution'` (HalaszRepAsm:314) — NOT
  kconv/dpoly_pow (finite×finite only; usable solely for pre-convolving
  the finite 𝒮·P·P legs). The ~5 expected helper layers, ENUMERATED so
  the executor recognizes them as anticipated: (1) shifted-coefficient
  LSeriesSummable at c₀ (trivial via finite support; smoothSeries_summable
  :205 is Re>1-stated — restate); (2) iterated LSeries_convolution'
  (𝒮·𝓛·P·P); (3) the norm-convolution summability for the
  hat_contour_rep gate; (4) reverse hat_contour_rep; (5) the
  t₀-centering compatibility. FAIL-FAST now trips on NEW sublemmas
  beyond this set (~6), not at 3. Fallback unchanged (multivariable-
  Perron port, D, campaign-gate).⟧
- **H-5** [C, 550] `hfactor_bridge`: ⟦R (HF-REF-B): TWO reconciliations,
  not one: (a) the SECONDARY terms — sound as designed, term-for-term
  MS-EXIT's LHS at x := X+h (re-verified: hatK ∈ [0,1], support ≤ X+h,
  the floor boundary clean, carriers exact); (b) NEW — the MAIN-TERM
  reconciliation: the seam is WINDOWED (1_{y<n<X/y}) while prop21RHS
  is full-F: the out-of-window main mass + the f-vs-ellLin(g)
  linearization defect must each be bounded-and-added-to-E or
  explicitly routed (coordinate with H-0's ruling). A survivor routed
  to HLOSS must be named, never silent.⟧
- **H-EXIT** [B, 150] `prop21_unconditional` — stated per H-0's
  ratified shape. The S1′ representation stands with the prime-datum
  relation explicit and every defect priced.

### ⟦A — THE H-WALL AMENDMENT (maestro-ruled, 2026-07-22 09:30; announce-then-fire)⟧

HID-BETA landed H-4 + the bonus `prop21RHS_hat_rep` (prop21RHS as the
hat-smoothed fourFactorCoeff sum, Jacobian-2 handled) and found the
main-term wall: the reconciliation CANNOT go per-coefficient (the
beta-integral couples the four convolution indices — verified against
GHS pp.8-11); the main term is extracted ONLY by the series-level FTC
collapse (= the landed seam_double_ftc), which requires the ALIGNED
(2.3)-form. Two stones are INSERTED before H-5:

- **H-1b** [C, ~400] `seam_realignment`: prop21RHS's symmetric form →
  the aligned (2.3)-form. DESIGN — THE HAT-REP SANDWICH: do NOT shift
  contours. The aligned form differs from the symmetric form by
  argument shifts in each factor = multiplicative reweightings
  n^{±alpha}, n^{±beta} of the CONVOLVED COEFFICIENTS (H-4's shiftCoeff
  infra); pass through the coefficient sum (line-independent by the
  exact kernel K2') — prop21RHS_hat_rep on one side, four_factor_hat_rep
  FORWARD on the realigned factors on the other; the identity is
  shiftCoeff algebra, zero analysis. Summability: the corner ledger's
  law (weights <= n^{2eta}; crude primorial-grade constants admissible
  INSIDE summability Props only). Validate the sandwich in scratch
  BEFORE building; STOP on any surprise (fail-fast ~3 new sublemmas).
- **H-5a** [B/C, ~300] `window_truncation_defect`: the P(s±beta) vs
  L(lambda_ell)(s±beta) truncation defect at the coefficient level,
  its mass routed to MS-B's budget (the freeze's woven-truncation
  ruling stands: the defect lives HERE, consumed by H-5(a)).

H-5 then fires seam_double_ftc on the realigned form (main term
telescopes; secondaries = MS-EXIT at x := X+h); H-EXIT unchanged.
The multivariable-Perron port remains the campaign-gate fallback if
the sandwich fails validation. (No dedicated refuter pass: the stone
reuses landed machinery and the sandwich is kernel-validated in
scratch before use — the tripwire is the refuter.)

### Corner ledger (Part 1)

- **x↔X truncation:** MS-EXIT sums over ⌊x⌋; the seam's hat-smoothed sum
  is a tsum with ramp support ≤ X+h — the defect terms live on
  n ≤ X+h; instantiate MS-EXIT at x := X+h (its regime allows x ≥ x₀;
  X+h ≥ X ≥ x₀ ✓). The h-ramp's partial terms are ≤ the full terms
  (0 ≤ hatK ≤ 1, termwise domination — no new mass).
- **t₀-twist in norms:** drops (norm_twist unimodular) — the reason
  MS-EXIT's t₀-free bound is the correct target. ✓ (Lift Map confirmed.)
- **α,β-shift coefficient weights:** n^{±α}, n^{±β} for α,β ∈ [0, 2η]:
  bounded by n^{2η} ≤ (X+h)^{2η} = e^{2η log(X+h)}-grade — MUST NOT be
  crudely absorbed (it's e^{O(log X/log y)} — HUGE). The design keeps
  the shifts INSIDE the exact identity (they cancel at the endpoint
  evaluations); only the DEFECT terms carry shifted exponents, and
  MS-B's statement already carries exactly those shifted exponents
  (the 2η+α rough / α-integrated shapes). Refuters: verify NO stone
  bounds a shifted coefficient crudely.
- **η vs 2η:** GHS's β→2β doubles the β-range; MS-B's exponents are
  stated at (2η+α) — consistent with the freeze's frozen targets ✓;
  the α-range after substitution is [0, η] ✓. Verify at H-1 (the
  Jacobian mandate).
- ⟦R (HF-REF-B)⟧ **summability-Prop admissibility:** a crude
  primorial(y)^{2η}-grade constant is admissible ONLY inside the
  summability Prop (the hat_contour_rep gate — a Prop, not a bound);
  it is FORBIDDEN in the defect-mass bound, which uses MS-EXIT
  verbatim.
- ⟦R (HF-REF-B)⟧ **the y-floor is doubly load-bearing:** y ≥ 8 serves
  MS-B's 1/(1−α) ≤ 2, AND the seam's y ≥ 10 keeps c₀−2η ≥ ~0.13 > 1's
  margin for the shifted smooth evaluations — future consumers must
  not lower y toward e².

═══════════════════════════════════════════════════════════════════
## PART 2 — L11-ASM (the keystone choreography)
═══════════════════════════════════════════════════════════════════

GOAL: `halasz_primes_pow` at the FROZEN header (HalaszPrimes.lean) +
P ≤ T^10 + ∃ C c T₀ outermost. EVERY ingredient is landed. Extends
`Salt/MR/HalaszPrimesCore.lean` (single writer, disjoint from Part 1).

- **A-1** [C, 500 ⟦R: re-priced from 400⟧] `per_pair_contour`: the
  reconciliation (L11-EDGE's step 1): rep_truncated's Icc-truncated
  vertical line vs pole_residue_term's rectBI — the rearrangement
  I·V_right = 2πi·windowMellin(1+iu) − (B_bot−B_top) + I·V_left
  ⟦R (ASM-REF): the orientation is VERIFIED correct as the freeze read
  it — signs independently derived and confirmed⟧. Pricing: left edge
  by `shifted_edge_price` × the P^{σ₀} kernel mass (∫(σ₀²+v²)⁻¹ ≤ π/σ₀
  ≤ 2π — σ₀ ≥ 1/2 guaranteed by the SIXTH threshold, see A-3);
  ⟦R (ASM-REF's kill): the HORIZONTALS cross Re = 1 where ζ′/ζ has NO
  crude bound (Σ Λ/n^x diverges at x < 1) — the original "kernel decay
  only" under-scoped. REPAIR: price the horizontals' ζ′/ζ by the region
  bound ‖ζ′/ζ‖ ≤ C_E·D₄(5T+1) uniform on Re ∈ [σ₀, 2] at heights
  ∈ [T, 5T] — moving RIGHT of the spine only increases the min-distance
  to zeros, so the spine disc-core bound holds a fortiori; realize via
  near_norm_logDeriv_Zc_le / a small edge-agnostic generalization of
  shifted_edge_disc_core. The horizontal total ≤ C_E·D₄·(c−σ₀)·kernel/T′²
  ~ D₄·P/T² — dominated by the C₂·P·log P/T term.⟧ The tail by TRUNC.
  Exit shape: ‖Σ_n Λ(n)n^{iu}·w(n) − windowKernel P 1 u‖ ≤
  C₁·P·exp(−(c_vk/2)·log P/D₃(5T+1))·D₄(5T+1) + C₂·P·log P/T + C₃·D₄·P/T².
  ⟦R note: on the left edge ζ′/ζ = logDeriv Zc − 1/(s−iu−1) — the pole
  part priced 1/dist per the l11 freeze; the stale :530-532 docstring
  (pre-W′ 5T) should be corrected in-comment while there.⟧
- **A-2** [B/C, 350] `dual_assembly`: window_dominates → the tsum→Finset
  split (finite support [1,⌊3P⌋]) → the prime-power discard
  (prime_power_discard at B = |𝒯|·Σ‖η‖² via inner_sum_sq_le) → open the
  square over pairs → |η_t η_{t′}| ≤ |η_t|²+|η_{t′}|² → the pole row
  (pole_row_sum, 44π, diagonal-inclusive) → the error row × |𝒯| →
  divide by log P (the direction chain: division on [P,2P] only).
- **A-3** [C, 400] `halasz_primes_pow`: the absorption + packaging:
  D₃(5T+1) → D₄(T) (ruling 1 + Amendment W′: log(5T+1) ≤ 2 log T at
  T ≥ 5; the (loglog)⁴-vs-³ slack + the outermost ∃C eat every constant
  incl. 44π, C₁-C₃, the √P discard at D₄ ≥ 3); the T₀ thresholds
  enumerated in the docstring — ⟦R (ASM-REF): SIX, not five: the strip
  T₁; exp(exp(~27/c_vk)); (loglog)⁴ ≤ (log)^{5/4}; the √P-absorption;
  the P = T^10 tail corner; and THE SIXTH — shifted_edge_price's own
  T₀ = max(max T₁ 3, exp(exp(9000·c_vk + c_vk/(2δ₀) + 1))), which is
  what actually guarantees σ₀ ≥ 1/2 for LARGE c_vk (the named #2
  SHRINKS as c_vk grows and cannot). Auto-inherited by destructuring
  shifted_edge_price — documentation, not proof change.⟧ P ≤ T^10
  inner; ∃ C c T₀ outermost (ASM-REF: all three existentials verified
  absolute — no quantifier forcing). The executor states the decay as
  exp(−c·log P/D₄(T)) with the ∃c per the freeze (the header's prose
  c = 1 is a prose gap, not the binding shape). THE FROZEN HEADER IS
  LAW — any resistance = STOP + report. ⟦R note: prime_power_discard
  may prove redundant (the pole/error rows already carry the full
  Λ-mass per window_dominates' structure) — the executor may discover
  the assembly needs no separate discard subtraction; either shape is
  acceptable, document which.⟧

### Corner ledger (Part 2)
All height evaluations at 5T+1 (Amendment W′) — never T, never |u|.
The diagonal is the pole row's u = 0 entry (the no-split law; NEVER
primePoly_wellspaced_l2). The u-sign symmetry via Zc_conj (landed).
The truncation-tail corner at P = T^10 exactly (REF-B's R-4 audit).

═══════════════════════════════════════════════════════════════════
## PART 3 — THE TERMINAL CHAIN (T-0 hhead → thm_A1′) + HLOSS
═══════════════════════════════════════════════════════════════════

- **T-0** [C, 500] `hhead_supplier` (Lift Step 3): assemble
  `prop21_unconditional` (Part 1) + `contour_A13_A14_head_wired`
  (K4-WIRE) + `s2_tail_ledger` (landed) into the concrete
  Uhead/Utail/hsplit discharging `halasz_ball_decay`'s three binders
  (HalaszCore:404-406) ⟹ **`halasz_ball_decay_unconditional`** ⟹
  `T1_pointwise_decay` unconditional. New file `Salt/MR/HalaszHead.lean`.
  ⟦R (TERM-REF's power-counting kill): **T-0b IS MANDATORY**, not
  conditional — the wired head's crude coefficient-mass² diagA has
  ZERO M-dependence (crude/sharp ~ (X/y)², and no supF can rescue
  e^{−M}); hhead is unreachable without the sharp diagonal.
  **T-0b** [C, 300]: sharpen k4_plan_le_diag to Σ‖bₙ‖²/n^{2c} using
  the exp(−c|log(m/n)|) off-diagonal decay ALREADY in
  dirichlet_plancherel; the landed grains: `dirichlet_poly_l2_mvt_final`
  (MVCore2:620 — the SHARP 2T+20N unconditional MVT, a strengthening
  the freeze didn't know it had) + `offdiag_int_bound` (⟦R citation
  fix: HalaszCore:195, NOT L2MVT⟧) + log_diff_ge. T-0b lands BEFORE
  T-0's assembly.⟧ ⟦R2 (T-WAVE's in-session correction): the literal
  target Σ‖bₙ‖²/n^{2c} is FALSE (the kernel exp(−c|log(m/n)|)(mn)^{−c}
  = max(m,n)^{−2c} has row-sum ≍ N — the MVT's intrinsic +N cannot
  vanish); the TRUE sharpening landed instead: (π/c)·(Σ‖bₙ‖/n^c)²,
  M-independent, retaining the separable (mn)^{−c}. Flagged, not
  forced — the honest-refusal law.⟧ ⟦R architecture note (verify at dispatch): ball_decay
  is applied with its f-slot = fgJ (1-bounded via norm_fgJ_le,
  non-multiplicative — type-checks); the analytic hhead/htail/hsplit
  must be established FOR fgJ through the prop21 seam, which is exactly
  what the S1′ chain supplies. State the target instantiation
  explicitly in the file docstring.⟧
- **T-1** [C, 400 — ⟦R: DESIGNED, the TERM-REF amendment, replacing
  design-first⟧] HLOSS RESOLVED — THE W VANISHES: TERM-REF's
  counterexample (f = costwist t₀: center distance 0 yet in-window
  defect ~ loglog X) kills the halve-minus-W route at resonant t₀ —
  AND exposes an iron-rule-1 drift: the landed dist_split_A4_frozen
  carries "−W" while the s8-freeze N2 FROZEN conclusion has NO W (the
  landed lemma is weaker than its frozen statement). THE AMENDED ROUTE
  (additive supersession, no landed edits): (i) BIND y = (log X)^{O(1)}
  (GHS p.11's own y = (log X)⁴; compatible with the seam's 10 ≤ y ≤ √X
  and hfactor's regime); (ii) re-derive the R3.1 floor AT THE FROZEN N2
  SHAPE via the window-restriction identity:
  𝔻(fgJ, costwist t)² ≥ 𝔻(f, costwist(t+t₀))² − (out-of-window mass),
  DROPPING the nonneg in-window part on the ≥ side; (iii) the
  out-of-window mass = Σ_{p≤y} 1/p + Σ_{X/y≤p≤X} 1/p = O(logloglog X)
  at polylog y (mertens_second_sharp twice) — absorbed by the frozen
  −5·logloglog slack. W disappears from the chain entirely; the
  frequency bookkeeping (the t in 𝔻(fgJ, costwist t) is already
  t₀-recentered) stated per the branch hypotheses. New lemmas in
  `Salt/MR/DistWindow.lean`; the −W versions remain landed but
  superseded.
- **T-2** [C, 700] the §8.3/A2 assembly (`Salt/MR/Prop1Assembly.lean`,
  NEW — the s8-freeze wave-4 shape re-validated against the landed
  corpus): int_U at P = exp((logX)^{1−1/48}), Q = exp(logX/loglogX),
  H = (logX)^{1/48}; the T0/T1 split (T1_pointwise_decay); E1 exact
  (T+N); the E_j moments (lemma13_moment landed); the large-T sub-rung
  (trivial MVT + prefactor absorption, [200]); terminal `prop_A3′`
  (M_range form, capped domain — the frozen statement from the
  s8-freeze/halasz sub-freeze).
- **T-2b** [B, 150 ⟦R (TERM-REF)⟧] `T1_pointwise_decay_corrected`: the
  composition variant taking the R3.1 CORRECTED floor ((1/32)loglogX −
  5logloglog − C, W now absent per T-1) and concluding the
  (logX)^{−1/64+o(1)} grade — the landed T1_pointwise_decay demands the
  clean floor and does not compose with the corrected one without this
  absorption lemma. (TERM-REF also confirms: the wave-4 parameters
  SURVIVE re-validation; the sharp MVT (dirichlet_poly_l2_mvt_final)
  is a strengthening over the freeze's feared T+NlogN.)
- **T-3** [C, 500] `thm_A2′` (`Salt/MR/ThmA2.lean`, NEW): the f-arm +
  f = 1-arm via R1.4's capped M_range (landed, DistHalasz:262).
- **T-4** [B, 300] `thm_A1′` (`Salt/MR/ThmA1.lean`, NEW): ⟦R (TERM-REF):
  built to the s8-freeze's PROVISIONAL shape — (1/X)∫|…|² ≤
  C(exp(−M/2) + (480 loglog h/log h)² + (logX)^{−c₀}), P₁ = (log h)^{480},
  Q₁ = h, η = 1/12 — with the honest caveat that S9's socket is a
  standing decision-register item (mr-freeze scope-diff 9 ratifies the
  qualitative general-f grade and FORBIDS pre-staging S9 statement
  pinning), so A4's final wording may adapt at the S9 block; the shape
  here is the ratified provisional target, not "verbatim-forever".⟧
  **THE BLOCK'S BOUNDARY** — S9→S10→S11 is the next block.

### Dispatch plan (post-refuters, the pipeline)
Wave α (parallel): H-1..H-3 (HalaszIdentity) ∥ A-1..A-3 (the keystone —
COULD CLOSE L11) ∥ T-0 (HalaszHead). Wave β: H-4..H-EXIT ∥ T-2. Wave γ:
T-3, T-4 (+T-0b/T-1 as ruled). Executors single-writer per file; the
full trap bank rides every brief.

## REFUTER ASSIGNMENTS (the workflow's kill-checks)

- **HF-REF-A** (Part 1, H-1..H-3): the four-factor factorization's
  exactness at the corner (does ellLin_split really give the seam's f;
  the gJ = windowIndicator vs the S1-B lambdaLin window — AUDIT the
  carrier identification against prop21RHS's actual windowSum);
  the FTC double-collapse's uniformity; the centering c-o-v's
  measure-theory (full-line translation + the β→2β Jacobian); the
  η-vs-2η bookkeeping.
- **HF-REF-B** (Part 1, H-4/H-5): the design insight's load test — can
  the four-factor product REALLY be treated as one Dirichlet series
  with convolution coefficients on the c₀-line (𝓛's infinite series ×
  three finite ones: absolute convergence, the swap's summability
  gate); the shifted-coefficient-weight corner (NO crude n^{2η}
  absorption anywhere); the bridge's term-for-term defect
  identification against MS-EXIT's exact LHS (regime x := X+h; the
  ⌊·⌋ boundary); the fail-fast tripwire adequacy.
- **ASM-REF** (Part 2): A-1's orientation/sign audit (rectBI convention
  vs the desired identity — derive the rearrangement independently);
  the exit-shape constants (π/σ₀ ≤ 2π at σ₀ ≥ 1/2 — verify σ₀ ≥ 1/2
  at T₀!); the A-3 absorption at every corner incl. P = T^10 and the
  44π; the five-threshold completeness.
- **TERM-REF** (Part 3): THE HLOSS CONSUMPTION STUDY (T-1's open
  question — read DistSplit + PropA3Core's actual W-usage and report
  what grade the floor tolerates); T-0's assembly against
  halasz_ball_decay's verbatim binders (does the wired head's majorant
  diagA suffice or is T-0b mandatory — rule it); T-2's parameter
  re-validation against the landed corpus (the s8-freeze shapes are
  10 days old — anything drifted?); the thm_A1′ frozen statement's
  present-tense consumability (S9's interface unchanged?).

## LAWS (all parts)
Frozen shapes: prop21_analog's statement (already frozen), the
halasz_primes_pow header, prop_A3′/thm_A2′/thm_A1′ per the s8-freeze —
iron rule 1 absolute. Growing quantities in-statement (#253). The full
trap bank in every brief. Zeno partials = success. Single writer per
file. NO-GIT (#244).

### ⟦A — AMENDMENT P21-3K: the kernel-line compensation (maestro-ruled
### 2026-07-22 ~16:20; the audit: NUM-REF dissent / TRANS-REF + SAT-REF
### confirm, 2-1; the P21-2X species and precedent)⟧

R-SCOPE's cosh counterexample (arithmetic CONFIRMED independently to
machine precision by NUM-REF) exposed that the frozen prop21RHS was a
HYBRID: GHS (2.5)'s post-line-move symmetric FACTORS against the
pre-move, (alpha,beta)-free hat kernel. The freeze's own mapping note
(HalaszSeam:59-60) shows the intended object was GHS (2.5) WITH its
kernel x^{s-alpha-beta}/(s-alpha-beta); the transcription dropped the
kernel's argument shift. SAT-REF: hfactor as frozen is UNSATISFIABLE
at MS-EXIT-sized E (worst-case positive coefficients, no cancellation
-- prop21_analog vacuous as stated). THE AMENDMENT (one token, :438):
hatKernel X h c0 (t-t0) becomes hatKernel X h (c0 - alpha - beta)
(t-t0). Series legs UNCHANGED (the L-leg keeps Re > 1 everywhere; the
kernel poles sit at the shifted argument, strictly left, clean).
Consequence (audited numerically): the kernel deposits N^{-(alpha+
beta)}, cancelling seam_realignment_hat's N^{alpha+beta} EXACTLY --
prop21RHS = 2*intint Sum alignedCoeff*hatK, GHS's genuine Prop-2.1
object; the wall under all three dead H-5 designs vanishes by
definition. NUM-REF's dissent honored as the STANDING TRIPWIRE: any
bridge reaching secondary-sized E without producing the N^{-(alpha+
beta)} compensation is provably wrong. Cone repair (P21-3K-EXEC):
the mismatched-line hat rep variant; prop21RHS_hat_rep re-proved to
the ALIGNED coefficient form; prop21_contour_leg; prop21_analog's
proof (statement text unchanged -- mention-only, the P21-2X
precedent). H-5 v4 design block follows ON the corrected object.

### ⟦A — AMENDMENT V5-0: the seam un-windowing (JYH-RATIFIED
### 2026-07-22 ~17:15 — frozen-conclusion tier, the day's one JYH gate)⟧

prop21_analog's hfactor (:485) and CONCLUSION (:488): the seam carrier
windowIndicator y (X/y) becomes the trivial indicator (fun _ => 1) --
H-EXIT delivers the FULL twisted hat-smoothed sum, GHS (2.2) faithful.
Grounds (CARRIER-SCOPE + REC-V4-REF, all verified): the windowed
conclusion is UNSATISFIABLE (Theta(X log y) undamped out-of-window
mass vs E = Theta(X log y/log X)); GHS never windows its main term
(the FTC forces the full endpoint); the consumption audit shows every
downstream link needs only 1-boundedness + DISTANCE, and the distance
converts EXACTLY at the trivial indicator (simpler than T-1's landed
approximation). The two windows disentangled: the P-leg window
(GHS-intrinsic, exact by joint support) is KEPT everywhere; only the
seam-coefficient window (our addition) is removed. DistWindow's T-1
chain stays landed (heritage + branch-floor use). The v5 ladder
follows (h5-v5-brief.md + the v5 design block).

### ⟦A — AMENDMENT B4: the grade re-freeze (JYH-RATIFIED 2026-07-23
### ~09:55)⟧

The grade interface (1+M)e^{-M} / (log X)^{-1/64} is re-frozen to
C*e^{-cM} / (log X)^{-c/32}-form with c = 1/e, across grade_EM /
halasz_ball_decay / T1_pointwise_decay / T1_decay_conditional_final.
Grounds (HPRET-SCOPE, exponent chain traced): 1/64 = (1/2)*(1/32)
conveniences, never load-bearing; the landed floor is 8x stronger
than consumed; the s8-freeze's OWN Decision D4 documents the
tolerance ('qualitative fixed-delta grade; consumers need only
o(loglog)') -- this amendment exercises D4's clause, superseding N3's
numerals per the freeze's own terms. The price buys the fully-
elementary route (B-ladder) to the last frontier stone; max-modulus
was ruled out mathematically (boundary-sup destroys the pointwise
decay). Final grade: (log X)^{-1/(32e)}-form, fixed positive delta.
