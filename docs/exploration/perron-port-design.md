# PP-0/PP-1 DESIGN SKELETON — the line move (the port's analytic core)

*Maestro design block, 2026-07-22 ~10:40, per PERRON-SCOPE's ladder
(its report: appended to the consult brief's record; GO-confidence
MEDIUM as pure Opus, HIGH with this skeleton first — hence this
skeleton). Refuter pass fires at the quota reset, wave on verdicts.
JYH pre-approved fire-tonight-post-reset.*

## The load-bearing geometric claim (verify FIRST — the C-0 stone)

Reconstructing GHS's move in pre-move coordinates: at contour Re s =
c₀ the four legs sit at arguments s, s+α, s+α+β, s+α+β (schematically
— 𝒮 unshifted, the two Λ-legs and 𝓛 at POSITIVE shifts), and the move
takes the contour DOWN to Re s = c₀−(α+β) before the substitution
u = s+(α+β) restores contour c₀ with the shifts redistributed (the
symmetric prop21RHS pattern). Consequence, if the corpus's
`alignedCoeff` argument pattern matches: **during the move, every
infinite leg's argument keeps Re ≥ c₀ + (positive margin)** — in GHS's
arrangement the 𝓛-leg's argument has Re ≥ c₀+β/2 > 1 throughout the
strip — and the kernel poles (s = 0, −1) sit strictly left of the
strip (c₀−(α+β) ≥ c₀−2η > 0 by the y ≥ 10 floor).

**THE CLEAN-STRIP CLAIM: the moved strip contains NO singularity of
the integrand.** No pole is crossed; the line move is pure Cauchy
translation; there is no residue term at all. The main term comes —
exactly as H-5 always intended — from firing the landed FTC collapse
on the PRE-MOVE form, where every infinite leg sits at Re > 1.

- **C-0** [the wave's first stone, ~30 ln of verification]: read
  `alignedCoeff`'s actual definition (HalaszIdentity) and GHS (2.4)→
  (2.5); write the argument table for all four legs at both contour
  ends and across the strip; confirm the clean-strip claim for OUR
  shift pattern (α+β full shift, the P21-2X [0,η]² ranges). If ANY
  infinite leg's argument dips to Re ≤ 1 inside the strip, or any
  kernel pole enters: STOP — the residue-general fallback (below)
  activates, and the maestro re-rules before anything else lands.

## PP-0 `hat_line_limit` [C, 400–600, file: Salt/MR/PerronPort.lean]

The generic two-line lemma. Shape (∃-free, hypotheses explicit):

For F : ℂ → ℂ analytic on the closed strip c′ ≤ Re ≤ c (0 < c′ ≤ c),
with the decay hypothesis ‖F(σ+it)‖ ≤ M/(1+t²) uniformly in σ on the
strip (our integrands: LSeries·hatKernel — the 1/(s(s+1)) supplies
1/t², the series legs are bounded on the strip by their abscissa/
finite-support facts):

  ∫_ℝ F(c+it) dt = ∫_ℝ F(c′+it) dt.

Proof skeleton: finite rectangle [c′,c]×[−R,R] via the LANDED
`rectBI_eq_zero_of_differentiableOn` (SW/ContourShift — analytic ⇒
boundary integral 0); horizontal edges ≤ (c−c′)·M/(1+R²) → 0; the
vertical truncations → the full-line integrals by dominated
convergence (dominating function M/(1+t²), the landed `hat_tail`
pattern). Deliver also the trivial corollary form with the
substitution built in (contour at c′ re-read as contour at c with
shifted arguments) — that is the form PP-1 consumes.

Tripwires: (a) the uniform-in-σ bound M must come from named corpus
facts (finite-support polynomial bounds + `abscissa_largeSeries_le_one`
territory + `hat_mellin_bound`); if any leg lacks a strip-uniform
bound, STOP and name it. (b) No maxHeartbeats above 4M without a
comment.

## PP-1 `hat_line_shift` [C, 500–800, PerronPort.lean + consume in HalaszIdentity]

Instantiate PP-0 at F := (the full aligned four-factor LSeries) ·
hatKernel, c := c₀, c′ := c₀−(α+β), for each (α,β) ∈ [0,η]²
(measurably in (α,β) — the ∫∫ needs the identity pointwise on the
square + integrability, the landed `summable_bounded_weight` +
kernel-L¹ pattern). Combined with `hat_contour_rep` at both ends and
`seam_realignment_hat`, the output is THE BRIDGE:

  Σ_N fourFactorCoeff(α,β)_N · hatK_N
    = ∫_t [pre-move four-factor form](c₀+it) · hatKernel dt

— prop21RHS's symmetric coefficient sum equals the PRE-MOVE integral
where every infinite leg sits at Re > 1. (The N^{α+β} weight is
consumed by the substitution — this is the honest version of what the
refuted dissolution tried to get by algebra: the weight moves into the
kernel through the contour translation, exactly as REP-REF said it
must.)

Tripwire: if C-0 has activated the fallback, PP-1 becomes the
residue-carrying version — ∫ − ∫ = 2πi·Σ residues — with each residue
enumerated and identified before anything downstream is stated
(maestro re-rules; do NOT absorb an unexplained residue into E).

## Downstream (the scoper's ladder, unchanged, Opus-reachable)

PP-2 `main_term_from_residue` → rename `main_term_from_ftc` under the
clean-strip claim: fire `seam_double_ftc`/`seam_alpha_collapse` on the
pre-move form (all infinite legs Re > 1 — their home regime; the
log-derivative truncation to the window = H-5a's defect, plus the
scoper's (X, X+h]/y window-ceiling sliver folded into the desmooth
pricing). PP-3 `window_defect_priced` (→ MS-B at the worst corner).
PP-4 `secondary_desmooth_pack` (MS-EXIT @ x := X+h + hat_desmooth,
every E-summand named). PP-EXIT `prop21_unconditional` (route (i);
iron-rule-1: prop21_analog consumed verbatim).

## Refuter charges (fire at reset, before the wave)

1. **STRIP-REF**: attack C-0/PP-1 — reconstruct the argument table
   independently from `alignedCoeff`'s Lean definition and GHS pp.
   9–11; is the strip truly clean for OUR shift pattern (not GHS's
   α+β/2 pattern — the P21-2X substitution changed the geometry)? Is
   the pre-move form's coefficient identity with fourFactorCoeff
   exactly `shiftCoeff`-compatible?
2. **EDGE-REF**: attack PP-0 — does every leg admit a strip-uniform
   1/t²-compatible bound from LANDED facts? (The 𝓛 leg on Re > 1:
   uniform boundedness near Re = 1⁺ is NOT free — Σ λ_ℓ(n)/n^{1+ε}
   grows as ε → 0; the bound M may depend on (α,β) through the
   distance-to-1 of the 𝓛-leg's argument. Is M's (α,β)-dependence
   harmless for the pointwise-then-integrate structure?) This is the
   likeliest genuine gap — price it, don't wave at it.

Verdicts per the house schema; wave fires on FIRE/REPAIR-THEN-FIRE
with repairs applied.
