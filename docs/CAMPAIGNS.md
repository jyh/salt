# THE ANNALS OF SALT — the campaign register
### One entry per campaign: goal, status, headline results (Lean names), the trail.
### Curated, high-level, updated at campaign transitions (the [ceremony ritual](OPERATIONS.md));
### [pilot.md](exploration/pilot.md) holds the fine grain, [flags.md](blueprints/flags.md)
### the catches. Seeded 2026-07-20 (v1, reconstructed from the ledgers; JYH-review welcome).

**Headline registry: [docs/RESULTS.md](RESULTS.md)** (lint: `scripts/results_lint.py`) — the
dated, lint-verified row-per-theorem register. **Read it before asserting absence.**

| # | Campaign | Goal | Status | Headline |
|---|---|---|---|---|
| 1 | [BRUN](../Salt/Brun/) (N-series) | Brun's theorem | ✅ | `BrunStatement` via `Salt.N6.N6_2`; `TwinCountingBigO` (`Salt.M5BigO.N5_3`) — [guide](blueprints/brun-guide.md) |
| 2 | [P0/P1](../Salt/BrunLower/) | first lower-bound sieve | ✅ | `twin_almost_prime` (Ω(n(n+2)) ≤ 20 i.o.) |
| 3 | [TWINBAR](../Salt/TwinBar/) | the k=2 impossibility | ✅ | `twin_bar` (M₂ ≤ 2log2), `no_twin_weight`, the M₃ bar |
| 4 | [SW GATE](../Salt/SW/) | unconditional Siegel–Walfisz | ✅ | `siegelWalfisz_holds`; Siegel/zero-theory/contour stack |
| 5 | [BV](../Salt/BV/) | Bombieri–Vinogradov chain | ✅ | `bounded_gaps_of_siegelWalfisz` → unconditional bounded gaps |
| 6 | [CHEN I+II](../Salt/Chen/) | Chen's two theorems | ✅ | `chen_headline` (p+2 = P₂ i.o.); [`chen_goldbach`](../Salt/Goldbach/ChenGoldbach.lean) (large even N = p+P₂) |
| 7 | [T-BAL](../Salt/SW/TBalR8.lean) | Deuring–Heilbronn repulsion | ✅ | `dh_repulsion_ordered` (b=680, k=14, σ₀=16/17, explicit c) |
| 8 | [VK](../Salt/Vk/) | zero-free regions | ✅ | `zeta_zero_free_region_littlewood` (first ever); `_pow` (θ=3/4, first in any PA); [`Salt.Vmvt.vmvt`](../Salt/Vmvt/) |
| 9 | [S5/MR-PRE](../Salt/MR/) | the pretentious floor | ✅ | `zeta_lower_all_t`; `lambda_nonpret` (residual retired 2026-07-19) |
| 10 | [ENTROPY SPINE](../Salt/Entropy/Chowla/) | log-Chowla two-point | ✅→door | [`log_chowla_two_door_only`](../Salt/Entropy/Chowla/SpineFinal.lean) — sole hypothesis = the MRT door |
| 11 | [FULCRUM](../Salt/Fulcrum/) | the minimized Siegel hypothesis | ✅ | `FulcrumQualityMin` (F, C⋆; reality derived, c₀ = 1/126848 certified); the Hunt ([1](exploration/fulcrum-pass1.md)·[2](exploration/fulcrum-pass2.md)·[3](exploration/fulcrum-pass3.md)); 4 walls |
| 12 | [DICHOTOMY (D1)](../Salt/Fulcrum/Dichotomy.lean) | TPC ∨ NoSiegelZeros | ✅(hEngine-cond.) | `fulcrum_dichotomy`; `not_fulcrum_implies_noSiegelZeros` unconditional |
| 13 | [HB-L2C](../Salt/HB/) | the engine keystone | ✅ | [`hb_l2c_master_unconditional`](../Salt/HB/L2cMasterUncond.lean) — bare packet, zero residuals; [freeze +5 amendments](exploration/l2c-freeze.md) |
| 14 | [WALL-3](../Salt/HB/SignChain.lean) | the exchange-rate wall | ✅ | `IsSignFunction` chain (60 decls at `9b6d06e`: 1 structure + 11 defs + 48 proved statements; extractor in [pi-package §A7](exploration/pi-package-0803.md)); `neutrality_rate`; λ = the neutrality point — [ratification](exploration/wall3-d4-ratified.md) |
| 15 | [Z / D4](../Salt/Parity/) | the parity gap as object | ✅ | `Z ⟺ TPC` (window); `sufficient_true_not_parityInv` (THE GAP THM); [census of ten](../Salt/Parity/Instances.lean) |
| 16 | [SPINE-BUDGET](exploration/spine-budget-freeze.md) | kill the t/g residual | ✅ | F0 (old residual proven unsatisfiable); `log_chowla_two_budget_head` (∀extraFloor) |
| 17 | [CHI-SIEVE](exploration/chi-sieve-freeze.md) | the L2c residual | ✅(dissolved) | both counts proven χ-blind through the frozen engine — the residual was unnecessary |
| 18 | [HALASZ-INFRA (K1)](exploration/halasz-infra-freeze.md) | Perron+λ_f infrastructure | 🔶 1 named core | [`halasz_ball_decay`](../Salt/MR/HalaszCore.lean) + the S1′ spine assembled (5 windmills dissolved); sole residual = **MULT-SHIU** (the multiplicative Shiu/Brun–Titchmarsh bound, GHS Lemma 2.4 — panel candidate) |
| 19 | [S8 / MR-CORE](exploration/s8-freeze.md) | thm_A1′ → the MRT door | 🔶 climbing | 19 [MR modules](../Salt/MR/) landed; K1/K2 walls down ([`mvHilbertUniform_holds`](../Salt/MR/MVCore2.lean) at sharp π — plausible PA-first); frontier: A2 + the PropA3/A3a assemblies → waves 4–6 (H3 ✅, TRUNC-PERRON ✅ 2026-07-20 night) |
| 20 | [THE PAPER](../papers/flagship/main.tex) | "Twin Primes and Siegel Zeros: a Fulcrum" | 🔶 in approval | submitted 2026-07-20; 19 round-2 refinements; [council rulings](exploration/council-brief-noon.md) |

## The standing laws & the method's record
255 numbered catches ([flags.md](blueprints/flags.md), the sole authority) · **zero wrong
proofs, all campaigns** · the freezes in [docs/exploration/](exploration/) · the ritual in
[OPERATIONS.md](OPERATIONS.md) · the roads in [roadmap.md](exploration/roadmap.md) · the
day the era turned: [the Dichotomy Day report](reports/dichotomy-day-report.md). Four
windmills dissolved on close inspection (the Fable cliff; R1.1's SOS wall; GS Lemma 7.1;
the raw sharp Perron) — the pattern is now law: scope before escalating (#255).

## The convergence points ahead
**SPINE**: S8 summits → `log_chowla_two` unconditional (first formal log-Chowla).
**CROWN**: HB-ENGINE assembles → `TPC ∨ NoSiegelZeros` with no hypothesis.
**PORTFOLIO** (post-planning-council): mixed-risk avenues incl. the Siegel-zero hunt
(the batcrazy ticket: anomalously small class numbers at enormous discriminants;
verified-computation infrastructure novel regardless of outcome).
