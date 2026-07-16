# SPRINT-2 TRACK A DESIGN — N(T)-local + the MmuRate trophy (FROZEN off S2-A-recon)

*2026-07-16. The recon (the ledger ~22:40) found: A1 ~70% landed
(disk-Jensen: entire_zero_count_le + M0zeta + the center lower bound);
the argument-principle route STRICTLY DOMINATED (multi-pole AP absent
from mathlib; Backlund D-tier) — Jensen wins; and the trophy
plausibly routes 3-4-1 + A2a + SHORT-segment transport, making Rb-4's
D a possible route artifact. The fork is isolated to T-1ζ.*

## The wave-1 nodes (SAFE under every outcome — dispatched)

- **A1-ab (C)**: the half-box disk count #{Re∈[½,1), |Im−t|≤1} ≤
  C·log(|t|+2) via entire_zero_count_le at the extended radius
  (R ≈ 1.9 sphere, still Re > 0 — the M0zeta-style growth extension);
  the t-small/t-large split at T₀ ≥ 1.5 (the pole-in-disk case by
  compactness/finiteness); WITH-multiplicity (the divisor sum —
  confirmed as the A1 reading, it must feed the ζ′/ζ sums).
  III.3″ witness: at T = 10⁶ the slot evaluates to ≈ 198 vs the true
  ≈ 4.4 — constant loose 45×, RATE correct (the wall needs the rate).
- **A1-c (C)**: the functional-equation fold (riemannZeta_one_sub) →
  the full box. No Re < 0 growth ever needed.
- **A2a/N1 (C)**: |ζ(σ+it)| ≤ C·log(|t|+2) near σ = 1 — the
  dTerm/zeta_shift log-refinement (truncate at N ~ t). The
  independently-reusable node (Rb-4 priced it; feeds 3-4-1).

## The gated fork (T-lo → T-1ζ) — SUB-RECON FIRST, no executor

- T-lo (C-risk): the quantitative 3-4-1 lower bound |ζ| ≥ c/log^k on
  the σ ≥ 1−δ contour (three_four_one + A2a + the zero-free region).
- **T-1ζ (C or D — THE FORK)**: poly-log |1/ζ| on the FULL shifted
  vertical contour. C if T-lo holds uniformly at σ = 1−δ, |v| ≤ T;
  D if it degrades near zero ordinates and forces the zero-avoiding
  (∃T′, unlanded) contour whose deformed harmonic sums need the
  scale-u density (= exactly Rb-4's wall, one level deeper). The
  sub-recon adjudicates the uniformity BEFORE any trophy dispatch.
- T-Mμ (C): MmuRate via the 1/ζ Perron contour (rectBI = 0; the
  landed spine reuses) — dispatches only if T-1ζ resolves C.

## Case space (the gate checks COMPLETENESS)
t small/large × the two half-boxes × the r<R margin × boundary zeros
(harmless for upper counts — no ε-shift needed, a Jensen advantage) ×
multiplicity (with-mult throughout) × [trophy only] the three σ-zones
× the well-spacing sub-case (5c — the fork's crux).

## Zeno note
The chain A1-ab → A1-c is two nodes with a declared terminal; the
trophy chain is gated at the fork per the registration clause. If
the fork resolves D, Track A reports A1 + A2a as the landed prefix +
the death-node map (the registered informative-failure outcome).

## AMENDMENT (post-fork, ~23:20): the trophy re-spec
The fork adjudicated C-GO-VARIANT. The deep T-1ζ is DEAD (confirmed
D — t^{4·10⁶}). The chain is now: **T-lo′** (|ζ| ≥ c/log⁷t at σ ≥
1 − c₄/log⁹t via the 3-4-1 anchor at σ₀ = 1 + a/log⁹t + Cauchy-ζ′
on r ≈ 1/log t + the ADDITIVE transport — margins verified at
a = 1, c₄ = 0.2) → **T-1ζ′** (poly-log on the shallow contour,
uniform — never within a density scale of any zero) → **T-Mμ**
(the Perron budget at log T = (log x)^{1/10}; the landed kernel
spine; rectBI = 0). Dependency: A2a ON THE STRIP σ ≥ 1 − c/log t.

## AMENDMENT 2 (post T-lo′, ~04:20): the T-1ζ′ statement freeze

T-lo′ LANDED first-attempt (zeta_lower_shallow: k = 7 exact, no
upper σ-cap — the whole half-plane right of the shallow contour is
covered at |t| ≥ 2). T-1ζ′ freezes as ONE Perron-consumable
statement (file Salt/SW/ZetaInvShallow.lean):

```lean
theorem zeta_inv_shallow : ∃ c₄ > 0, ∃ C > 0, ∀ σ t : ℝ,
    1 - c₄ / Real.log (|t| + 2) ^ 9 ≤ σ → (σ : ℂ) + t * I ≠ 1 →
    ‖(riemannZeta ((σ : ℂ) + t * I))⁻¹‖ ≤ C * Real.log (|t| + 2) ^ 7
```

Case space (complete, the anti-Zeno enumeration):
1. |t| ≥ 2 — a corollary of zeta_lower_shallow (destructure its
   ⟨c₄₀, c⟩; ‖1/ζ‖ ≤ L⁷/c).
2. |t| < 2, σ ≤ 3 — the compact pole-patch: ζ⁻¹ = (s−1)/Zc on
   s ≠ 1; Zc analytic and NONVANISHING on the patch (Zc(1) = 1;
   elsewhere ζ ≠ 0 — σ ≥ 1 from mathlib, σ < 1 from the landed
   zero-free region at the tiny c₄); compactness → ‖Zc‖ ≥ δ > 0 →
   ‖1/ζ‖ ≤ 3/δ.
3. |t| < 2, σ ≥ 3 — the tail: ‖ζ − 1‖ ≤ ζ(3) − 1 < 1/2 →
   ‖1/ζ‖ ≤ 2.
s = 1 excluded by hypothesis (the Perron contour never passes
through it: the vertical line has Re ≠ 1, the horizontals have
Im ≠ 0).

COMPATIBILITY CHECK (pre-build, III.3″-style): the patch must sit
inside the landed zero-free region — c₄ ≤ c0·log⁸(2) with the S3d
c0 = 1/50456 requires c₄ ≲ 1.5e−6; the inherited c₄₀ ≈ 2.7e−20
passes with ~14 orders of margin. If the landed region's shape
differs from σ ≥ 1 − c0/log(|t|+2), STOP AND FLAG.

Consumer note (why one statement suffices): T-Mμ's straight-line
contour σ_T = 1 − c₄/log⁹T satisfies σ_T ≥ 1 − c₄/log⁹(|t|+2) for
all |t| ≤ T − 2 (monotonicity of log), and both horizontal edges
have σ ≥ σ_T — so the single half-plane statement above covers the
entire Perron rectangle boundary.

III.3″ witnesses (in-file mpmath docstring): t = 0 (deepest patch
point, near-pole — 1/|ζ| small), t = 1 (patch interior, off-pole),
t = 10⁶ (the corollary region).

PB-floor (sanctioned): if the compact patch stalls, land the
|t| ≥ 2 corollary alone as zeta_inv_shallow_large_t + flag.
