# Q6a-4 DESIGN BRIEF — MmuRate from the landed corpus (PRE-RECON)

*2026-07-15. Status: RECON DISPATCHED; design freeze + adversarial gate
AFTER the recon reports. Provenance: Q6a-3's stop-and-flag (the
exploration ledger ~12:00) — the wall currently ships conditional on
`MmuRate : ∀ A > 0, ∃ C x₀, ∀ y ≥ x₀, |M_μ(y)| ≤ C·y/(log y)^A`
(Salt/TwinBar/LambdaRate.lean). Landing MmuRate restores the gate
amendment's UNCONDITIONAL wall.*

## Two candidate routes (the recon adjudicates)

**R-a — the elementary Landau bootstrap from ψ** (the classical
equivalent-forms direction). Skeleton:
- L1 (B): `μ·log = −(μ ∗ Λ)` — from mathlib's `Λ = μ ∗ log`
  (vonMangoldt divisor-sum) by the Dirichlet-derivation identity;
  finite divisor-sum manipulation.
- L2 (B): `M(x)·log x = Σ_{n≤x} μ(n)·log n + O(x)` — the
  `Σ log(x/n) ≤ x` crumb (integral comparison).
- L3 (B): the summatory swap `Σ_{n≤x}(μ∗Λ)(n) = Σ_m Λ(m)·M(⌊x/m⌋)
  = Σ_d μ(d)·ψ(⌊x/d⌋)` — the landed Mlambda-fold pattern
  (sum_filter/sum_comm), cheap.
- L4 (**C, THE HEART, possibly D**): the effective bootstrap — from
  `|ψ(t) − t| ≤ K·t/(log t)^B` (landed, every B) and the L1–L3
  recurrence, extract `|M(y)| ≤ C·y/(log y)^A`. The naive insertion
  LOSES a log (the Σ1/d over the middle range); the honest argument
  is the Landau/Tenenbaum iteration (replace Λ by its average via the
  ψ-error, bootstrap the sup-norm of M through the recurrence). The
  constant-chase must be worked BEFORE freezing — this is exactly the
  kind of node where a plausible statement hides a false intermediate.

**R-b — Perron against 1/ζ, reusing the SW contour machinery.** The
corpus already owns: the quantitative zero-free region (S3d,
c₀ = 1/50456), the zeta partial-fraction bounds (Z2zeta, C₇ = 1080),
and a full effective-Perron pipeline built for ψ (−ζ′/ζ). The
classical effective `M(x) ≪ x·exp(−c√log x)` (which implies every
log-power rate) runs the SAME contour against `1/ζ`; the new
ingredients are lower bounds for `|ζ|` (equivalently upper bounds for
`|1/ζ|`) in the zero-free region — pieces of which S3d-era files may
already contain — plus the Perron truncation for a bounded-by-1
coefficient sequence (EASIER than Λ). If the pipeline is genuinely
re-runnable with `1/ζ` in the integrand slot, R-b may be CHEAPER than
L4 and more reusable (it would hand the corpus effective M_μ, m_μ,
and the machinery for any future Dirichlet-series coefficient sums).

## The recon's questions (dispatched, read-only)

1. Inventory the SW/Z2zeta contour spine: is the Perron scaffold
   generic in the integrand, or ψ-hardwired (which files, which
   interfaces)? What exactly would `1/ζ` need that `−ζ′/ζ` didn't
   (the `|1/ζ|` bound in the region — present or absent)?
2. For R-a/L4: does mathlib (or the corpus) have Abel
   summation/partial summation in a consumable form
   (`Finset.sum_Ioc_by_parts`-grade)? Sketch the bootstrap's
   constant-chase at A = 1 concretely; identify the intermediate that
   fails first if any.
3. Recommend R-a vs R-b with node decomposition + difficulty classes
   + cost estimates anchored to landed analogues (the SW contour
   nodes for R-b; the Mlambda fold for R-a's L3).

## Discipline

MmuRate's statement is FROZEN as written in LambdaRate.lean — the
design chooses the route, never the target. Statement changes would
regress the wall's conditionality contract and are Fable/human-only
per the iron rules. The design freeze that follows the recon gets an
adversarial gate before any executor dispatch (C-tier).
