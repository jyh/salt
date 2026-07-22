# THE PERRON-GATE DISSOLUTION — the windowed route

*Maestro design block, 2026-07-22 ~10:05. Status: DRAFT — refuter pass
dispatched (mandatory; verdicts land here). Supersedes the "GHS Lemma
2.5 port" framing of the H-wall if it survives. Inputs: HID-BETA's wall
(the β-integral couples the convolution indices; main term extracts
only via the series-level FTC), HID-GAMMA's landed sandwich algebra
(`seam_realignment`, `seam_realignment_hat`) + landed defect object
(`window_truncation_defect`, `norm_window_truncation_defect_le`), the
landed hat-rep infrastructure (`four_factor_hat_rep`,
`prop21RHS_hat_rep`, `LSeriesSummable_of_finite_support`), the landed
collapse (`seam_double_ftc` + `largeSeries_ftc_double_beta`), MULT-SHIU
complete (MS-A/MS-B/MS-EXIT).*

## The observation (why the gate dissolves)

Three landed facts compose:

1. **The residual IS the line shift.** The hat-smoothed sum at line c
   reads `Σ a_N·N^{−c}·ramp_N`. GAMMA's `seam_realignment_hat` gives
   `Σ fourFactorCoeff_N·N^{−c₀}·ramp = Σ alignedCoeff_N·N^{α+β}·N^{−c₀}
   ·ramp = Σ alignedCoeff_N·N^{−(c₀−α−β)}·ramp` — i.e. the symmetric
   hat sum at c₀ EQUALS the aligned hat sum at the shifted line
   c_{α,β} = c₀−(α+β), as exact coefficient algebra. Nothing needs to
   "cancel"; the weight is the reinterpretation.
2. **The shifted line is only forbidden to the infinite leg.** The
   aligned INTEGRAL form at c_{α,β} needs the hat rep's summability
   hypothesis there. The three finite legs (𝒮, P, P) are entire; only
   the full 𝓛 = LSeries(λ_ℓ) leg (re > 1 only) blocks it.
3. **The infinite leg can exit at c₀, where everything converges.**
   H-5a's defect object swaps 𝓛 ↔ windowed 𝓛_w AT LINE c₀ (re = c₀ >
   1: valid), with the defect's coefficient mass dominated by exactly
   MS-B's triple-sum shape (landed: `norm_window_truncation_defect_le`).

Order of operations is everything — this is the whole design:

```
prop21RHS  (full 𝓛, line c₀)
   │  W-1: swap 𝓛 → 𝓛_w at c₀  [valid: re > 1]      defect → MS-B
   ▼
windowed prop21RHS  (ALL FOUR LEGS FINITE, line c₀)
   │  W-0: sandwich, free for finite support        exact, zero analysis
   ▼
aligned windowed integral at c_{α,β}                [finite ⇒ converges
   │  W-2/W-3: the FTC collapse (windowed)           on EVERY line]
   ▼
endpoint differences  + enumerated windowed defects  → MS-A/MS-B
   │  W-4: route (i) reconciliation
   ▼
the seam's Σ fgJ·hatK  + priced E                    = hfactor discharged
```

No contour of any infinite object is ever moved. GHS Lemma 2.5 (truncate
at T, move the line, price the truncation) is REPLACED by "swap first,
then shift finite objects for free." The Perron port remains the
fallback, demoted to insurance.

## The stones

- **W-0** [B, ~150] `windowed_hat_rep_any_line`: for finite-support
  coefficients `a`, the hat rep holds at EVERY real line c:
  `∫_t alignedSeriesW(c+it)·hatK(t−t₀) dt = Σ_N a_N·N^{−c}·ramp_N`.
  Rides `LSeriesSummable_of_finite_support` + the landed
  `hat_contour_rep` (check: its hypothesis is stated as summability,
  not re > 1 — if a re-restriction is baked in, restate the finite
  version from the kernel identity directly). Combined with
  `seam_realignment_hat`: the sandwich COMPLETES for windowed objects.
- **W-1** [B/C, ~300] `prop21RHS_windowed_swap`: prop21RHS =
  windowed-prop21RHS + defectTerm, with `‖defectTerm‖ ≤` the ∫∫ of the
  H-5a defect mass. The (α,β)-shift weights inside the defect at c₀
  are ≤ N^{2η}-grade — admissible INSIDE summability/bound Props only
  (corner-ledger law); the exponent pattern must match MS-B's `2η+α`
  summand (GAMMA verified the shape at fixed (α,β); this stone
  integrates it over [0,η]² with the 2-Jacobian).
- **W-2** [C, ~350] the windowed FTC witnesses: `windowSum_ftc_double_beta`
  (finite analog of the landed `largeSeries_ftc_double_beta`) and the
  windowed `shifted_dirichlet_ftc` leg — termwise differentiation of
  FINITE sums (interchange is `Finset.sum` differentiation, no
  dominated convergence). Strictly easier than the landed infinite
  versions.
- **W-3** [C, ~550] `windowed_collapse`: fire `seam_double_ftc`'s
  PATTERN (not the lemma itself — its 𝓛-legs are full) on the windowed
  aligned form: the β-leg via W-2, the α-leg with 𝒮 fixed at s (the
  aligned form guarantees constancy). Every place the full-𝓛 proof
  used an identity that windowing breaks becomes a NAMED defect term —
  enumerate them (expected: the boundary terms of the windowed
  log-derivative structure). FAIL-FAST at ~4 unanticipated defect
  species: STOP + report (the enumeration is the design's testable
  claim).
- **W-4** [C, ~450] `hfactor_bridge` + **H-EXIT** [B, ~150]
  `prop21_unconditional`: endpoints reconcile to the seam under route
  (i) (`smoothPart_ellLin_eq_restrictBelow`; linearization defect
  vanishes); out-of-window main mass bounded-and-added; ALL defects
  (W-1's swap + W-3's collapse species) priced into E via MS-EXIT at
  x := X+h. E's final shape recorded in the docstring, every summand
  named. The S1′ representation stands.

## Corner ledger

- **The swap's double integral**: W-1's defect bound integrates a
  fixed-(α,β) bound over [0,η]²·(2-Jacobian). The bound must be
  UNIFORM in (α,β) on the compact square or monotone in the exponents;
  MS-B's summand carries the sup exponent 2η — check the worst corner
  (α = β = η), not the origin.
- **W-0's hypothesis audit**: if `hat_contour_rep` hard-codes c₀ > 1
  anywhere (even vacuously for finite support), the finite restatement
  must re-derive from the kernel identity — budget it as +100 ln, not
  a wall.
- **Endpoint β = η vs β = 2η**: the P21-2X Jacobian (β→2β) moved the
  endpoints; the collapse's endpoint evaluations must be read against
  the AMENDED prop21RHS (the (2:ℝ)• smul + [0,η] ranges). Off-by-two
  in the endpoint is the likeliest silent error in W-3/W-4.
- **The t₀-centering**: rides `seam_centering` (landed); the windowed
  swap commutes with centering (coefficient-level; check once in W-1).
- **What the dissolution does NOT claim**: no bound on the full 𝓛 off
  re > 1 is ever used or implied; the zero-free region never enters
  Part 1 (it lives in Part 2). If any stone finds itself reaching for
  ζ-theory, the design is being misread — STOP.

## Refuter charges (pass dispatched 2026-07-22)

1. **REP-REF**: attack W-0 — is the landed hat rep's hypothesis truly
   just summability? Does the kernel identity's derivation itself
   assume re > 1 (e.g. via an absolutely-convergent rearrangement that
   silently needs it)? Verify the finite-support case stands alone.
2. **SWAP-REF**: attack W-1 — the ∫∫ of the defect: uniformity on the
   square, the 2η+α exponent match to MS-B at the worst corner, the
   2-Jacobian bookkeeping, the centering commutation.
3. **WFTC-REF**: attack W-2/W-3 — does the collapse's telescoping
   structure survive windowing, or does a windowed leg break a
   convolution identity the full proof needs silently? Enumerate the
   expected defect species independently; compare counts.
4. **END-REF**: attack W-4 + iron-rule-1 audit — endpoint arithmetic
   against the AMENDED prop21RHS (the factor 2, the [0,η] ranges);
   route (i) instantiation; E's summands vs MS-EXIT's regime
   (x := X+h ≥ x₀); no frozen statement drift anywhere in the plan.

Verdicts: CONFIRMED-FATAL / CONFIRMED-REPAIRABLE / UNFOUNDED per
charge; overall FIRE / REPAIR-THEN-FIRE / HOLD.

## Fallback (if the dissolution is refuted)

The single-series truncated-Perron port (GHS Lemma 2.5 for ONE
Dirichlet series against the exact kernel): D-tier, JYH-consulted
before dispatch, with H-5a's banked defect and H-4's single-series
reduction still applying. The dissolution failing does not un-land
anything; every stone above that survives refutation stays valuable.
