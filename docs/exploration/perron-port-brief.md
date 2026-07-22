# CONSULT BRIEF — the single-series truncated-Perron port (Lemma 2.5)

*For JYH's evening read, 2026-07-22. The decision this brief serves:
approve (or sequence) the LAST analytic core of Part 1. Per the
refuted design block's own fallback clause, the port does not dispatch
without your word. A read-only PERRON-SCOPE reconnaissance is in
flight to ground this brief with the source's actual contour geometry;
its findings will be appended.*

## What the refutation settled (why this is now truly the only route)

The main-term extraction needs two properties no single object has:
**telescoping** (the log-derivative identity −𝓛′ = L(λ_lin)·𝓛 — an
Euler-product fact, true only for the FULL multiplicative series) and
**convergence on the shifted line** (true only for the WINDOWED finite
polynomial). WFTC-REF proved these mutually exclusive at the
structural level (window indicators are not multiplicative). The only
bridge is analytic: keep the full series, truncate the CONTOUR at
height T, move the line where the integrand is controlled, price the
truncation — GHS Lemma 2.5.

## What has already shrunk (the good news inventory, all kernel-checked)

- **Single series**: H-4 collapsed the four-factor product to ONE
  Dirichlet series with convolved coefficients (`four_factor_hat_rep`,
  `prop21RHS_hat_rep`). The port is not multivariable.
- **The exact kernel decays**: hatKernel carries 1/(s(s+1)) — 1/t²
  decay — so truncation tails are absolutely convergent integrals, not
  conditionally convergent Perron oscillation. This is where the
  D-tier may soften toward C; the scoper will price it.
- **The defect is banked**: H-5a's window-truncation defect object +
  its MS-B-shaped mass bound are landed.
- **Bookkeeping verified**: END-REF confirmed the P21-2X factor-2
  lands exactly once, and MS-EXIT's regime admits x := X+h.
- **The sandwich algebra is real**: `seam_realignment_hat` gives the
  exact reweighted form the contour argument must integrate.

## Open unknowns (the scoper's targets)

1. GHS's precise contour geometry at (2.4)→(2.5), pp. 9–11: which
   rectangle, which direction, what is bounded on the horizontals.
2. Whether the 1/t² kernel decay lets the truncation pricing bypass
   the classical Perron error terms entirely.
3. The interaction with the (α,β) double integral: uniformity of the
   truncation errors over the square (SWAP-REF's argument-vs-line
   lesson applies: track each factor's ARGUMENT, not "the line").
4. What the moved-line integrand needs: expected — only convergence
   facts about 𝓛 at re > 1 plus finite-polynomial growth; the
   zero-free region should NOT enter Part 1 (if the scoper finds
   otherwise, that is a STOP-grade surprise).

## Estimate (honest, pre-scoper)

Scoper: landed by the time you read this (Opus, ~80–150k). The port
itself: C/D-tier, ~1.5–3k lines, 2–3 executors, ~600k–1M tokens, 1–2
days at current cadence. Sequencing options: (a) fire on your word
tonight; (b) sequence after Part 2 (L11) closes so the fleet finishes
one front first. Maestro lean: (a) — Part 3 already waits on H-EXIT
alone, and the port is Part 1's last stone.

## The decision requested

Approve the port (and its timing), or hold for further design. Nothing
else in the campaign is blocked on your answer — L11 proceeds, Part 3
is assembled to its single residual, the cloud rehearsal runs.


## APPENDED — PERRON-SCOPE's findings (landed ~10:35)

Headlines: (1) zeta-theory and the zero-free region CONFIRMED OUT of
Part 1 (the move lives in re ∈ (0, c₀], infinite legs never below
re = 1). (2) The exact hat kernel DISSOLVES Lemma 2.5's entire
truncation apparatus — the Perron min(1, 1/(T|log(x/N)|)) oscillation,
the near-x Shiu short-interval sums (GHS's hardest piece), the height
truncation, the horizontal edges: ALL VANISH. (3) The surviving
obligations: the line move itself (PP-0/PP-1, design-tier), the
window defect (banked, MS-B-shaped), the (2.4) secondary (LANDED:
MS-EXIT verified shaped exactly to GHS's two terms), the desmooth
(landed). (4) One execution flag: the (X, X+h]/y window-ceiling
sliver, fold into desmooth. (5) GO-confidence MEDIUM as pure Opus,
HIGH with the Fable PP-0/PP-1 skeleton first — the skeleton is now
written: docs/exploration/perron-port-design.md (incl. the CLEAN-STRIP
claim: in pre-move coordinates no pole is crossed at all — the line
move is pure Cauchy translation and the 'main-term residue' language
dissolves into the FTC endpoints, verified as stone C-0 first).
Estimate: ~1.9-2.9k lines, ~700k-1.1M tokens, matching the envelope.
