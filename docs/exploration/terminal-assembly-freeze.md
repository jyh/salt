# THE TERMINAL ASSEMBLY FREEZE — S8's last design block

*Maestro design block, 2026-07-22 morning (JYH-ratified: lift-first, the
thm_A1′ boundary). Status: DESIGNED, refuter pass launching (the
refuter-pass workflow's first passenger). Inputs: THE LIFT MAP (pilot
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

### The ladder (order fixed; ~2.0-2.8k ln total)

- **H-1** [C, 300] `seam_four_factor_pointwise`: at s = c₀+it, the seam
  series factorizes: seamDirichlet f gJ t₀ s = (the four-factor product
  at the α=β=0 corner) via `ellLin_split` + `lseries_ellLin_eq_smooth_mul_large`
  (LANDED) + the window's f = s ⋆ ℓ decomposition; the t₀-twist carried
  as the coefficient twist (norm_twist, landed).
- **H-2** [C, 350] `seam_double_ftc`: the (α,β) double-integral collapse —
  the β-leg IS `largeSeries_ftc_double_beta` (LANDED witness,
  HalaszFactor:109); the α-leg is its mirror (`shifted_dirichlet_ftc` at
  the α-variable, same landed engine); combined:
  ∫∫ (four-factor with 𝓛′-slots) dβ dα = the endpoint-difference form
  that recovers H-1's corner. (GHS p.8's two FTC steps, exactly.)
- **H-3** [B/C, 400] `seam_centering`: the n^{-it₀} centering
  change-of-variables (the full-line t-translation: ∫_t F(t)·hatKernel(t−t₀)
  = ∫_t F(t+t₀)·hatKernel(t) — measure-preserving, `intervalIntegral`/
  `MeasureTheory.integral_comp_add_right`) + the β→2β substitution +
  c_{α,β} = c₀−α−β/2 symmetric-shift bookkeeping (GHS p.10; the scoper's
  resistance #3, priced landable; the private twistCoeff template
  re-derived in-file as `seamShift`).
- **H-4** [C, 600, THE RISK STONE] `four_factor_hat_rep`: prop21RHS's
  inner t-integral = the hat-smoothed sum of the four-fold convolved
  coefficients, per the design insight above. Route: express each factor
  as a finite/absolutely-convergent Dirichlet series on the c₀-line
  (𝒮, P finite — entire; 𝓛 convergent at Re > 1); the product's
  coefficients via the convolution algebra (`Finset.Nat.sum_divisors`-
  family / the kconv pattern); `hat_contour_rep` + `kernel_sum_swap` for
  the ∫_t ↔ Σ swap. FAIL-FAST: if the four-fold convolution algebra
  exceeds ~3 helper layers, STOP and report — the fallback is the
  scoper's original multivariable-Perron port (D, campaign-gate).
- **H-5** [C, 450] `hfactor_bridge`: the triangle-inequality assembly:
  the EXACT identity (H-1..H-4) reduces the hfactor difference to the
  WINDOW-TRUNCATION DEFECT (the y < n < x/y support cut on the Λ_ℓ
  window — GHS §2.2's tailoring), whose coefficient-norm mass is
  TERM-FOR-TERM the GHS-(2.4) secondary terms (MS-REF-B's R-4 verdict:
  "FIT EXACT") = `mult_shiu_MS_EXIT`'s LHS. Consume MS-EXIT; the
  regime hypotheses (8 ≤ y, η = 1/log y) supplied by the seam's own
  y-regime (10 ≤ y ≤ √X per HalaszSeam:31 — covers).
- **H-EXIT** [B, 150] `prop21_unconditional`: `prop21_analog` with
  hfactor DISCHARGED. The S1′ representation stands hypothesis-free.

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
  the α-range after substitution is [0, η] ✓. Verify at H-3.

═══════════════════════════════════════════════════════════════════
## PART 2 — L11-ASM (the keystone choreography)
═══════════════════════════════════════════════════════════════════

GOAL: `halasz_primes_pow` at the FROZEN header (HalaszPrimes.lean) +
P ≤ T^10 + ∃ C c T₀ outermost. EVERY ingredient is landed. Extends
`Salt/MR/HalaszPrimesCore.lean` (single writer, disjoint from Part 1).

- **A-1** [C, 400] `per_pair_contour`: the reconciliation (L11-EDGE's
  step 1): rep_truncated's Icc-truncated vertical line vs pole_residue_term's
  rectBI — the rectangle identity rearranged to: (truncated line) =
  2πi·windowMellin(1+iu) − (left edge) − (horizontals) + (truncation
  defect), then priced: left edge by `shifted_edge_price` × the P^{σ₀}
  kernel mass (norm_windowKernel_le at abscissa σ₀; ∫(σ₀²+v²)⁻¹ ≤ π/σ₀);
  horizontals by the kernel quadratic decay (P-grade/T′²); the tail by
  TRUNC. Exit shape: ‖Σ_n Λ(n)n^{iu}·w(n) − windowKernel P 1 u‖ ≤
  C₁·P·exp(−(c_vk/2)·log P/D₃(5T+1))·D₄(5T+1) + C₂·P·log P/T + C₃·P/T².
  ORIENTATION AUDIT MANDATORY: rectBI's sign convention
  (bottom−top+I·right−I·left) against the desired line integral —
  L11-EDGE's beta-reduction trap notes apply.
- **A-2** [B/C, 350] `dual_assembly`: window_dominates → the tsum→Finset
  split (finite support [1,⌊3P⌋]) → the prime-power discard
  (prime_power_discard at B = |𝒯|·Σ‖η‖² via inner_sum_sq_le) → open the
  square over pairs → |η_t η_{t′}| ≤ |η_t|²+|η_{t′}|² → the pole row
  (pole_row_sum, 44π, diagonal-inclusive) → the error row × |𝒯| →
  divide by log P (the direction chain: division on [P,2P] only).
- **A-3** [C, 400] `halasz_primes_pow`: the absorption + packaging:
  D₃(5T+1) → D₄(T) (ruling 1 + Amendment W′: log(5T+1) ≤ 2 log T at
  T ≥ 5; the (loglog)⁴-vs-³ slack eats every constant incl. 44π, C₁-C₃,
  the √P discard at D₄ ≥ 3); the FIVE T₀ thresholds enumerated in the
  docstring (the strip T₁; exp(exp(~27/c_vk)); (loglog)⁴ ≤ (log)^{5/4};
  the √P-absorption; the P = T^10 tail corner); P ≤ T^10 inner; ∃ C c T₀
  outermost. THE FROZEN HEADER IS LAW — any resistance = STOP + report.

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
  NOTE the K4-WIRE scope finding: the wired head's diagA is the
  coefficient-mass² majorant; if the R2.4-sharp diagonal is demanded
  here, the wave-I-3 offdiag stone (ball_mvt remainder,
  offdiag_int_bound landed in L2MVT) is the named supplement — priced
  [C, 300] as T-0b, dispatched only if T-0's assembly demands it
  (fail-fast will tell).
- **T-1** [DESIGN-FIRST, scouted in the refuter pass] HLOSS-WINDOW:
  the in-window twist-defect Σ_{y<p<X/y}(1−Re(|f p|²p^{it₀}))/p. The
  OPEN question (honest): the trivial bound is 2·(loglog X)-grade,
  which would DESTROY the (1/32)loglog floor in dist_split_A4_frozen —
  so the consumption must absorb W differently (branch structure,
  recentering, or W entering only in regimes where the floor has
  slack). TERM-REF's assignment: the consumption study (how do the
  dist_split branches actually use W; what W-grade does the frozen
  R3.1 conclusion tolerate; is the twist-defect ≤ 𝔻-distance algebra
  that the branch hypotheses already dominate?). T-1's design lands as
  a freeze AMENDMENT after the verdict — NOT guessed here.
- **T-2** [C, 700] the §8.3/A2 assembly (`Salt/MR/Prop1Assembly.lean`,
  NEW — the s8-freeze wave-4 shape re-validated against the landed
  corpus): int_U at P = exp((logX)^{1−1/48}), Q = exp(logX/loglogX),
  H = (logX)^{1/48}; the T0/T1 split (T1_pointwise_decay); E1 exact
  (T+N); the E_j moments (lemma13_moment landed); the large-T sub-rung
  (trivial MVT + prefactor absorption, [200]); terminal `prop_A3′`
  (M_range form, capped domain — the frozen statement from the
  s8-freeze/halasz sub-freeze).
- **T-3** [C, 500] `thm_A2′` (`Salt/MR/ThmA2.lean`, NEW): the f-arm +
  f = 1-arm via R1.4's capped M_range (landed, DistHalasz:262).
- **T-4** [B, 300] `thm_A1′` (`Salt/MR/ThmA1.lean`, NEW): the S9
  interface, the s8-freeze's frozen statement verbatim: (1/X)∫|…|² ≤
  C(exp(−M/2) + (480 loglog h/log h)² + (logX)^{−c₀}), P₁ = (log h)^{480},
  Q₁ = h, η = 1/12. **THE BLOCK'S BOUNDARY** — S9→S10→S11 is the next
  block.

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
