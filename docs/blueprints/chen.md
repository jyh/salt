# The Chen rung — `p + 2 = P₂` modulo SW (`chen`)

*Fable, 2026-07-12. ROUTE FREEZE after the three-scout recon
(`wf_ecc8ad60-c46`: sources / P2-scope / switching — full reports in the
session workflow journal). Constants below marked ⏳ are PENDING the
page-image transcription pass (the recon worked from pdftotext; the P0
lesson (#16) makes page-image verification mandatory pre-dispatch).
Headline: **`chen_of_siegelWalfisz : SiegelWalfisz → {p | p.Prime ∧
(p+2).factorization-is-P₂}.Infinite`** (twin form; the exact P₂
carrier is a statement-design decision at C5, options: `∃ q₁ q₂,
Prime q₁ ∧ Prime q₂ ∧ p + 2 = q₁ * q₂ ∨ Prime (p+2)` with both factors
> p^{1/8}, matching Tao's native form). The day the SW arc lands, this
becomes unconditional Chen alongside unconditional bounded gaps.*

## Catch #20 (the recon's headline correction)

`parity-frontier.md` implied margin `log 3 − ½log 6 ≈ 0.203`. WRONG as
an assembly margin: the switch costs `½c̄ ≈ 0.1815`. TRUE margin:

**`M := log 3 − ½·log 6 − ½·c̄ ≈ 0.0212`** (1.9% relative), with
`c̄ = ∫_{1/8}^{1/3} log(2−3t)/(t(1−t)) dt = 0.363083729… < 0.363084`
(BJS Lemma 52 citable cross-check; certificate node C4a).

**The budget-ledger doctrine (mandatory, twinbar/T1 precedent):** the
sensitivity equation is `1.0986·δ_f + 0.8959·δ_F + 0.1815·δ_sw +
(absolute slop)/(Π₂x/(4 log z)) < 0.0212` — a RUNG-LEVEL ledger, not
per-node. Node C0 freezes the allocation table (each of the seven o(1)
sites gets an explicit slack budget summing under M) BEFORE any wave-2+
dispatch; every executor's landed constant is checked against its row.

## The frozen route (Tao 254A Supp. 5 §3 = Opera de Cribro ch. 25; the
explicit-constants backbone = Bordignon–Johnston–Starichkova (BJS),
arXiv:2207.09452v6 — reconcile v6 against Nathanson ch. 10 at
page-image level pre-freeze)

Parameters: `z := x^{1/8}`, `y := x^{1/3}`, level `D := x^{1/2−ε}`.
Do NOT retune to H-R/Halberstam's `z = x^{1/10}` (needs `f(5)` —
outside the elementary window, forces an extra iterate).

- **Chen's weights** (Tao Lemma 11, valid `x^{2/3} < n ≤ x`):
  `1_{P₂}(n) ≥ 1 − ½Σ_{p≤y} 1_{p∣n} − ½Σ_{p₁≤y<p₂≤p₃} 1_{n=p₁p₂p₃}
  − ½Σ_{p≤y} 1_{p²∣n}`.
- **Reduction (38)**: `A₁ − ½Σ_{z≤p≤y} A_{2,p} − ½A₃ ≫ x/log x` over
  `x/2 ≤ n ≤ x−2`, carriers `A₁ = ΣΛ(n)·1_{(n+2,P(z))=1}` etc.
- **BV input (39)**: `Σ_{d≤D} |r_d| ≪ x log^{−10} x` for the Λ-in-APs
  remainders at `E_d = {−2 mod d}`, `g(2) = 0, g(p) = 1/(p−1)` — the
  EXACT output shape of our SW-gated BV chain
  (`Salt/BV/psi_BV_of_siegelWalfisz'`; PsiToPi-style conversion node).
- **A₁** (lower linear sieve at `s = 4−8ε`): `≥ (log 3 − o(1))·Π₂·x/
  (2 log z)` (uses `f(4) = (e^γ/2)log 3`-equivalent, stated
  V(z)-relative).
- **A₂** (upper sieve, per-prime level `D/p`): `≤ (log 6 + o(1))·Π₂·x/
  (2 log z)` via `∫₁^{8/3} dt/(t(4−t)) = (log 6)/4`.
- **A₃** (THE SWITCH): sift `E'_d = {+2 mod d}` on
  `a_n = 1_{[x/2+2,x]}·Σ 1_{n=p₁p₂p₃}` (`z≤p₁≤y<p₂≤p₃`); level-D
  distribution via GENERAL BV for triple convolutions of
  primes-in-intervals with an SW-regular factor; upper sieve at
  `s = 1+ε`; PNT double-integral count ⇒ `≤ (c̄ + o(1))·Π₂·x/(2 log z)`.
- **Assembly**: `LHS ≥ (2log3 − log6 − c̄)·Π₂·x/(4 log z) > 0`.

## The linear-sieve freeze (P2, serving this rung and P3/P4 forever)

**BJS Theorem 6** (both sides, explicit): `F, f` DEFINED by the
elementary Rosser-chain series `fₙ` (Nathanson Thm 9.4 lineage — an
explicit recursion, NO delay-differential equations, NO e^γ, NO
Mertens-3rd), remainder `R = Σ_{d∣P(z), d<QD} |r(d)|` with the
`εC_i(ε)e²h(s)` slack shape (⏳ the `C₁, C₂` tables and `h(s)`
breakpoints at page-image level). Everything V(z)-relative (P0's O-free
doctrine); the closed forms `2e^γ/s` (on (1,3]) and `(2e^γ/s)log(s−1)`
(on [2,4]) are DOCUMENTATION, never Lean statements. Do NOT attempt the
series = closed-form identification (Jurkat–Richert Selberg-seed
cluster in disguise, D-adjacent). Hypothesis (4) (the V-ratio/Mertens
input) is served by the landed PM1 windowed Mertens nearly verbatim
(the Σ1/p → ∏(1−g(p))⁻¹ log-bridge via PM2's pointwise pattern; keep
the Q-set general in the freeze).

**Known errata (transcribe-time traps, from the recon):** Nathanson
Thm 10.3 is missing a factor 2 in `U_N` (BJS p. 36 fn. 4); Thm 10.2
needs the `q ∤ N` side condition (BJS fn. 3); Yamada arXiv:1511.03409
is BROKEN at (87)/(104) — never consult; Tao's lower-bound half (his
(13)) is Exercise 10 — BJS Thm 6 is the proved source for BOTH sides.

## The general-BV freeze discipline (P4 keystone)

The corpus trap to avoid (V2.LS-bil, struck 2026-07-11): do NOT freeze
the maximal form. The switching consumer needs strictly LESS: fixed
scale (support `[x/2+2, x]`), fixed residue (`±2 mod d`), `L¹` in `d`
(not max-over-y), `d` squarefree dividing `P(y)` up to `D` (ALL such
`d` — the dyadic gluing lives in the assembly node, not the freeze).
Freeze the Prop-13 shape with the SW-regularity of the convolution
factor as a NAMED HYPOTHESIS; the β-SW derivation (ψ-form cumulative
gate → unweighted prime indicator on `[N, λN]` with coprimality
insertion: ψ→θ + Abel log-removal + the `(log N)^C` vs `(log x)^C`
threading) is its own C node (the corpus' PsiToPi/AbelCore precedent —
an adaptation, not a copy).

## Node DAG (waves; ~40–70 nodes cumulative with P2; multi-session)

| id | content | class |
|---|---|---|
| C0 | the margin budget ledger: the sensitivity table with per-site slack allocations (seven o(1) sites), frozen numerically | B (Fable+numeric) |
| C1a | BJS `fₙ`/Rosser-chain defs + the elementary recursion + monotonicity | B/C |
| C1b | the `h(s)`/tail machinery + the `c_n` certified tail (n ≈ 80–100 at 2-decimal precision, rational interval ops — the T1 CertEval axis; prototype margins show 60–90% headroom so coarse certification suffices) | C (compute-heavy) |
| C1c | **BJS Theorem 6** — the two-sided linear sieve at the frozen windows | C+ (keystone 1) |
| C1d | hypothesis (4) discharge via PM1/PM2 (the log-bridge) | B/C |
| C2a | A₁ at the twin sequence: the BV input (39) from the SW-gated chain + C1c lower side | C |
| C2b | A₂: the per-prime-level upper applications + the `∫dt/(t(4−t))` grid (PM1 serves the q-sum) | C |
| C3a | **general BV, weak form** (fixed scale/residue, L¹, SW-hypothesis-named) — Vaughan + large sieve + dispersion pipeline reuse | C+ (keystone 2) |
| C3b | β-SW: the interval prime-indicator derivation from the gate | C |
| C3c | the fine-partition bookkeeping (λ = 1+log^{−20}x blocks, diagonal absorption, explicit-K budgets per the DispersionClose precedent) | C |
| C3d | the PNT double-integral count of `Σa_n` | C |
| C4a | the `c̄ < 0.363084` integral certificate (elementary, interval-arithmetic-friendly) | B (numeric) |
| C4b | prime-power strip + the `x^{2/3}` threshold trivia | A/B |
| C5 | assembly → **`chen_of_siegelWalfisz`** | C |

PB-floors: C1c alone is a standalone mathlib-first artifact (the first
formal Rosser–Iwaniec linear sieve); C3a alone upgrades the BV corpus
to convolutions (serves any future E₂/E₃ work); if the razor assembly
stalls, the floor is `p + 2 = P₄`-shape at the same architecture with
slack margins (state honestly, flag). The optimality/parity section of
BJS stays OUT (not needed).

## Pre-dispatch gates
1. ⏳ page-image transcription of BJS Thm 6 + the C_i/h tables + Lemmas
   32/37/52 (+ the Nathanson reconciliation) — in flight.
2. The C0 ledger freeze (needs 1).
3. The adversarial gate workflow on this blueprint (ultracode; multiple
   lenses: statement fidelity vs the sources, the budget arithmetic,
   the V2.LS-bil-trap check on C3a's freeze, interface fit against
   Salt/BV + PM1/PM2 + the sieve carriers).
Only then wave 1 (C0/C1a/C1b/C4a in parallel).
