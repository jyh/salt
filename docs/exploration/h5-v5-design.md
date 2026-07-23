# H-5 v5 — THE UNWINDOWED ALIGNED ROUTE (the final assembly)

*Maestro design block, 2026-07-22 ~17:35. Status: DRAFT — refuter pass
firing concurrently with V5-SURGEON (the V5-0 surgery). Foundation:
V5-0 (JYH-RATIFIED), prop21RHS_hat_rep_aligned (LANDED), FTC-V4-REF's
verified-sound collapse core + its specified repair, CARRIER-SCOPE's
consumption audit. This supersedes h5-v4-design.md (HOLD); v4's sound
parts are inherited explicitly below.*

## The target (H-EXIT's final shape)

`‖Σ' n, seamCoeff f (trivial) t₀ n · hatK X h n − prop21RHS g t₀ X h c₀ y η‖ ≤ E`
under route (i) (f = ellLin g) + the regime (incl. 0 < c₀ − 2η).
The full twisted hat-smoothed sum — GHS (2.2). No coefficient window
anywhere on the seam side; the P-leg window stays inside prop21RHS.

## The stones (post-surgery; dependency order)

- **V5-2** [C, ~450] `aligned_collapse_full`: on
  `prop21RHS_hat_rep_aligned`, with FTC-V4-REF's repair built in:
  (a) FIRST the joint un-truncation (V5-3's lemma): both winCoeff
  legs → full lambdaLin(restrictAbove) EXACTLY on N ≤ X; the ramp
  region (X, X+h] residue routed to V5-5, NAMED. (b) THEN the landed
  full-leg collapse: β-leg via seam_double_ftc / shifted_dirichlet_ftc
  at range 2η composed with beta_double_jacobian (the 1/2 meets the
  leading (2:ℝ)• — work the constant chain in notes BEFORE Lean;
  endpoints at 2β ∈ {0, 2η}); α-leg via seam_alpha_collapse on the
  FULL log-derivative (never shifted_dirichlet_ftc on windowed P —
  the v4 error). (c) Exit: prop21RHS = (main endpoint 𝒮·𝓛(w) form)
  − (η-endpoint → MS-A shape) − (2η-endpoint with the full Λ-leg →
  MS-B shape) − (V5-5's ramp residue), each summand NAMED.
- **V5-3** [B, ~150] `joint_support_untruncation`: on the hat support
  N ≤ X+h with two indices prime-supported > y and the smooth index
  < y: if N ≤ X, every index < X/y (GHS §2.2's argument verbatim:
  two partners > y force the rest < X/y); hence winCoeff = full
  lambdaLin coefficient-wise on the four-factor convolution at
  N ≤ X. State the ramp complement (X < N ≤ X+h) as the explicit
  residual set. Elementary Finset/support work, zero analysis.
- **V5-4** [C, ~300] `endpoint_reconciliation_full`: the collapsed
  main endpoint Σ (𝒮∗𝓛-coefficients)·twist·hatK vs
  Σ seamCoeff f (trivial) t₀·hatK under route (i):
  smoothPart_ellLin_eq_restrictBelow + the full ellLin smooth×rough
  factorization (ellLin_split family). OUT-OF-WINDOW TERM = ZERO by
  construction (full vs full). The t₀-centering via seam_centering.
  Expected residual: none beyond bookkeeping — if a nonzero
  structural residual appears, STOP (it would contradict
  CARRIER-SCOPE's Q2 map; maestro re-rules).
- **V5-5** [B/C, ~200] `ramp_sliver_bound`: the (X, X+h] hat-ramp
  residue of the un-truncation. THE JOINT STRUCTURE NOTE: with both
  window legs present, a sliver index k > X/y forces its window
  partner l into (y, y·(X+h)/X] — a near-empty range — so the true
  mass is far below REC-V4-REF's crude (h/y)·log X (which ignored
  the joint constraint). The executor exploits the SAME joint
  argument on the ramp; target: ≤ E-grade with room. If the honest
  bound still exceeds E-grade at small y: STOP + report the exact
  mass (maestro re-rules the regime split). hat_desmooth is NOT
  applicable (1-bounded hypothesis vs log-grade lambdaLin — REC's
  verified exclusion); build the log-grade variant.
- **V5-6** [B, ~150] `hfactor_discharged` + **H-EXIT**
  `prop21_unconditional`: E assembled — MS-A + MS-B via
  mult_shiu_MS_EXIT at x := X+h + V5-5's sliver + the desmooth
  pieces; H-EXIT stated at the V5-0 shape, route (i), the regime
  gates threaded (0 < c₀−2η included). Every E-summand named in the
  docstring. THE S1′ REPRESENTATION STANDS.
- **V5-7** [B, ~150] `unwindowed_scaffolds`: T1_decay/hhead_supplier
  variants at the trivial-indicator seam + the EXACT distance
  identity pretDistSq(seamCoeff f trivial t₀)(costwist t) X =
  pretDistSq f (costwist (t+t₀)) X (no out-of-window mass — the
  twist-shift algebra only). The fgJ versions stay landed (heritage).

## Corner ledger

- **The 2η endpoints** (the P21-2X ghost, again): β-FTC over [0,η]
  on 𝓛(w+α+2β) gives endpoints {0, 2η}; any η-endpoint on the β-leg
  is a dropped Jacobian — STOP.
- **The constant chain**: (2:ℝ)• × (1/2 from ∂β = 2𝓛′) × the MS-A/B
  normalizations — one page of arithmetic in the executor's notes
  before any Lean; END-REF verified the 2 lands once in the v4-era
  audit, but the un-truncation reorders steps — re-verify.
- **NUM-REF's standing tripwire**: the N^{−(α+β)} compensation must
  trace to the amended definition in every chain.
- **The sliver at small y**: V5-5's STOP clause is the only regime
  risk; everything else is regime-uniform.
- **No ζ-theory in Part 1**; the zero-free region enters only Part 2.

## Refuter charges (firing concurrently with the surgeon)

1. **COLLAPSE-V5-REF**: attack V5-2/V5-3 — state the joint-support
   lemma yourself from GHS §2.2 and check the four-factor convolution
   support arithmetic (incl. the n=1 smooth index edge and
   prime-power indices); the composed FTC at 2η + Jacobian constant
   chain; the endpoint census against MS-A :1427 / MS-B :2209 EXACT
   shapes (index-by-index).
2. **SLIVER-V5-REF**: attack V5-4/V5-5/V5-7 — the zero-defect claim
   of the full-vs-full reconciliation (derive the 𝒮∗𝓛 coefficients
   under route (i) and match seamCoeff at the trivial indicator
   EXACTLY, edge conventions included); the sliver's TRUE mass with
   the joint constraint (numerics encouraged — is it E-grade at
   y = 10 and at y = (log X)^A?); the exact distance identity's
   twist algebra; the E census for silent survivors.

Wave fires on FIRE / REPAIR-THEN-FIRE with repairs applied, after
BOTH the surgeon lands green and the verdicts return.
