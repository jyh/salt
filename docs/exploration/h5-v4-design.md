# H-5 v4 — THE ALIGNED ROUTE ON THE CORRECTED OBJECT

*Maestro design block, 2026-07-22 ~16:40. Status: DRAFT — refuter pass
firing (mandatory). This is the freeze's ORIGINAL H-5 design revived:
P21-3K removed the wall that killed v1-v3, and the foundation lemma
`prop21RHS_hat_rep_aligned` (LANDED, 3-axiom) now supplies exactly the
object the original design assumed it had. Nearly every ingredient
below is ALREADY LANDED; this block is an assembly plan, not new
analysis. NUM-REF's standing tripwire governs: the compensation
N^{−(α+β)} is now IN the definition — no stone may re-drop it.*

## The state after P21-3K

`prop21RHS = 2•∫∫_{[0,η]²} Σ_N alignedCoeff(α,β)_N·hatK_N` — GHS's
genuine Prop-2.1 main object. The hfactor target (prop21_analog,
statement UNTOUCHED): `‖seam-hat-integral − prop21RHS‖ ≤ E` with E =
the MS-EXIT budget. The aligned legs (per STRIP-REF's verified table):
`𝒮(w)·P(w+α)·P(w+α+2β)·𝓛(w+α+2β)` — 𝒮 fixed at w (the FTC's
requirement), every infinite-leg argument at Re ≥ c₀+2β·0 = c₀ > 1
across the whole square. The FTC's home regime, at last reached.

## The stones

- **V4-1** [B, ~150] `aligned_hat_rep_matched`: the MATCHED-line rep
  for the aligned series at c₀: Σ alignedCoeff·hatK =
  (1/2π)∫_t alignedSeries(c₀+it)·hatKernel(X,h,c₀,t−t₀) dt.
  Rides `LSeries_convolution'`-family + `hat_contour_rep` exactly as
  `four_factor_hat_rep` did (same five layers, aligned arguments);
  summability at c₀: the 𝓛-leg at Re = c₀+α+2β ≥ c₀ > 1 ✓, finite
  legs by support. (If `four_factor_hat_rep`'s proof generalizes by
  parameter-renaming, do that — do not re-derive.)
- **V4-2** [C, ~450] `aligned_collapse`: pull 𝒮(w)·hatKernel out of
  the ∫∫ (both (α,β)-free — THE point of the alignment + amendment);
  fire the landed collapse on the inner double integral of
  P(w+α)·P(w+α+2β)·𝓛(w+α+2β):
  - β-leg: P·𝓛 at the SAME argument = the windowed log-derivative
    against the full 𝓛. The EXACT identity is
    P·𝓛 = −(1/2)·∂_β[𝓛] + (P − P_full)·𝓛 where P_full = the full
    log-derivative series: the first term FTCs
    (`largeSeries_ftc_double_beta`, LANDED), the second is H-5a's
    defect object (`window_truncation_defect`, LANDED, MS-B-shaped
    mass) times 𝓛 — CARRIED EXPLICITLY as a named term, never
    assumed small here (WFTC-REF's law: no windowed log-derivative
    identity exists; the defect is the honest remainder).
  - α-leg on the β-endpoint terms: `shifted_dirichlet_ftc` (LANDED)
    on P(w+α)·𝓛(w+α) → 𝓛(w)−𝓛(w+η); the 2η-shifted endpoint term
    becomes GHS Term 3's shape (sec₂).
  - Exit shape: prop21RHS = (1/2π)∫_t 𝒮·[𝓛(w) − Term2(w) − Term3(w)
    − windowDefectTerms(w)]·hatKernel dt, every subtracted term NAMED.
- **V4-3** [C, ~400] `endpoint_reconciliation`: the main endpoint
  (1/2π)∫ 𝒮(w)·𝓛(w)·hatKernel = Σ (𝒮∗𝓛-coefficients)·hatK vs the
  seam's Σ fgJ·hatK: route (i) (`smoothPart_ellLin_eq_restrictBelow`,
  LANDED — the linearization defect vanishes at f = ellLin g) +
  `fgJ_eq_window_mul`/`seam_carrier_factorization` (LANDED) + the
  out-of-window mass (DistWindow's LANDED chain) + the (X, X+h]/y
  window-ceiling sliver folded into `hat_desmooth` (LANDED). Corner:
  the t₀-centering rides `seam_centering` (LANDED).
- **V4-4** [B/C, ~300] `hfactor_discharged` + **H-EXIT** [B, ~150]
  `prop21_unconditional`: assemble E — sec₁ → MS-A, sec₂ → MS-B,
  window defects → MS-B's summand, out-of-window + sliver → the
  DistWindow/desmooth bounds — all via `mult_shiu_MS_EXIT` at
  x := X+h (regime verified by END-REF). State H-EXIT per route (i)
  with the regime hypotheses (incl. the new 0 < c₀−2η gate). E's
  every summand named in the docstring. THE S1′ REPRESENTATION
  STANDS.

## Corner ledger

- **β vs 2β endpoints** (the P21-2X ghost): the aligned 𝓛-leg sits at
  w+α+2β; the β-FTC over [0,η] produces endpoints at 2β ∈ {0, 2η} —
  Terms at 𝓛(w+α) and 𝓛(w+α+2η). Any stone finding endpoints at η
  instead of 2η has dropped the Jacobian — STOP and recheck against
  `beta_double_jacobian` (LANDED).
- **The ∂_β factor**: ∂_β[𝓛(w+α+2β)] = 2·𝓛′(w+α+2β) — the 2 must
  meet the definition's leading (2:ℝ)• correctly; work the constant
  chain on paper in the executor's notes BEFORE the Lean.
- **The defect's α,β-dependence in V4-2**: (P−P_full)·𝓛 under the
  ∫∫ carries weights ≤ N^{2η}-grade inside its mass bound — the
  corner-ledger law (admissible inside Props only); MS-B's summand
  carries the matching 2η+α exponents (GAMMA verified).
- **NUM-REF's tripwire**: every stone's exit must trace the
  N^{−(α+β)} compensation to the definition, never to a proof step.
  If any chain seems to work WITHOUT the amendment having mattered,
  it is wrong — stop.
- **No ζ-theory**: nothing here touches the zero-free region; if a
  stone reaches for it, the design is misread — STOP.

## Refuter charges (firing now)

1. **FTC-V4-REF**: attack V4-2 — derive the exact windowed-vs-full
   split identity independently; is P·𝓛 = −(1/2)∂β𝓛 + defect·𝓛 the
   right shape with GAMMA's alignedCoeff (P at w+α+2β is the SECOND
   window leg — check WHICH leg carries the log-derivative role and
   whether both P-legs' roles are correctly assigned in the collapse);
   the 2β Jacobian chain; the α-leg's applicability
   (shifted_dirichlet_ftc's hypotheses at our arguments).
2. **REC-V4-REF**: attack V4-3/V4-4 — the endpoint 𝒮·𝓛 coefficient
   sum vs fgJ under route (i): exact match or residual (work the
   convolution identity against fgJ_factorization's actual Lean
   form); the out-of-window/sliver/desmooth coverage; E's summand
   census vs MS-EXIT's statement; the new 0 < c₀−2η gate's threading
   into prop21_unconditional's regime.

Verdicts per the house schema; the wave fires on FIRE /
REPAIR-THEN-FIRE with repairs applied (announce-then-fire; the
pipeline's standing order).

## Fallback

None needed beyond the standing one: if a genuine wall appears, it is
by construction a NEW fact (the old wall is definitionally dead), and
it comes back to the maestro. The Lemma-2.5 port apparatus (PP-0
shelved lemma, the scoper's map) remains shelf inventory.
