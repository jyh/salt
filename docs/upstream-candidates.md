# Mathlib upstream candidates (registry)

Maintained by the house; tiers per the ratified 3-tier workflow
(see docs/reports/gold-window-report.md §Recommendations and the
writeup plan). Criteria: mathlib-clean statement (no salt-specific
defs), independent value, review surface manageable.

## Tier 1 — ready, small, high-value

- **`Salt.SW.sum_divisors_eq_hyperbola_symm`** (Hyperbola.lean)
  — the symmetric √N Dirichlet hyperbola identity,
  CommRing-general, EXACT. Fills the explicit TODO at
  `Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:428`.
  Zero salt imports in the statement. The obvious first PR.
- **`Salt.Vk.log_series_remainder`** (Taylor.lean) — the sharp
  `|log(1+u) − Σ_{j≤k}(−1)^{j−1}u^j/j| ≤ u^{k+1}/(k+1)` for
  u ≥ 0. Mathlib's `Real.abs_log_sub_add_sum_range_le` carries
  a 1/(1−|x|) blow-up (catch #128); this is strictly sharper on
  [0,1) and the proof (FTC + geom_sum) is self-contained.
- **`Salt.Vmvt.primes_in_Ioc_eff`** (PrimeEff.lean) — the
  effective Chebyshev interval count y/(8 log y) ≤
  #primes(y,2y] for y ≥ 2²², explicit threshold, from the
  Bertrand valuation lemmas. Mathlib has Bertrand's postulate
  but no effective COUNT.

## Tier 2 — the milestone (larger review surface)

- **`Salt.Vmvt.vmvt`** + the Vmvt track (Defs → Linnik →
  Transversal* → StepFull → Summit2) — the Vinogradov Mean
  Value Theorem, elementary route. A mathlib milestone; needs
  a dedicated upstreaming arc (naming, generalization passes,
  splitting). Suppliers worth extracting standalone:
  `linnik_lemma`, `integral_norm_pow_eq_Jk` (the Parseval
  bridge), `desigFibre_card_le`.

## Tier 3 — the analytic-NT toolkit

- `Salt.Mertens.mertens_third` (+ the M = γ − B chain) —
  believed first-anywhere; explicit rate.
- `Salt.ExpSum.kusmin_landau` (C = 1), the vdC second/third/
  k-th derivative tests, `zeta_block_bound`,
  `zeta_strip_family` (post-VK, as a family).
- `Salt.SW.zeta_partial_em` + `zetaApprox_strip` (the sharp
  strip EM across the real axis).
- `Salt.Maynard.card_divisors_le_rpow`,
  `copHarmonic_uniform_lower`, `sum_tau_in_ap_le` (Shiu's
  theorem, restricted form).
- `Salt.SW.abs_mwWeighted_le_div_log` (Σμ(d)/d rate) and the
  Barban–Vehov / Graham lemmas (survey which forms are
  mathlib-shaped).

## Process

One PR at a time from tier 1; each PR's salt-side lemma gets a
deprecation note pointing at the mathlib name once merged. Do
NOT hold salt work on upstream review latency.
