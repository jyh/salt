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
(absolute slop) < M = 0.0211907` — a RUNG-LEVEL ledger, not per-node.

## C0 — THE FROZEN LEDGER (gate-corrected 2026-07-12; catches #21–#23)

**Global freeze: `ε_sieve = 1/10000`** (BJS Table 1: C₁ = 106,
C₂ = 108; admissible ≤ 1/74). NOT 1/200 (catch #21: at 1/200 the
sieve slack totals 21×M — the A₂ site alone 14×M; 1/2000 still
1.51×M; Table 1 has no usable intermediate row — do NOT interpolate,
C-monotonicity is unstated). `ε_sieve` is DECOUPLED from the level
deficit `ε'` in `D = x^{1/2−ε'}` (keep ε' ≈ 1/200 there; the retreat
f(4)−f(4−8ε') is inside S7). Operating points: A₁ lower s = 4−8ε'
(D ≥ z² ✓); A₂ uppers s_p ∈ [4/3, 3] (h hits the e⁻² plateau for
p ≥ x^{1/4−ε'}); A₃ switch **on P(y) at s = logD*/log y → 3/2⁻**
(Lemma 32's level; F(3/2)·e^{−γ}·(3/4) = 1.000000 exactly — the
sieve constant absorbs into c̄).

| site | mathematical site | cap (M-abs) | justification at ε_sieve = 1/10000 |
|---|---|---|---|
| S1 | A₁ Thm-6 slack εC₂e²h(4) + f(4)-series cert (C1b) | 0.0022 | slack = 0.112% rel; cert: odd-trunc N ≥ 23 w/ Table-2 cₙ (tail ≤ 4.3e−4) |
| S2 | A₂ aggregated slack εC₁e²·J, J = ∫h(4−8t)dt/t = 0.0949632 | 0.0055 | δ_F = 0.466% rel; headroom covers F-grid cert + Σ_p→∫ error |
| S3 | A₃ switch slack at s = 3/2 (e²h = 1) | 0.0015 | δ_sw = εC₁·3/(4e^γ) = 0.446% |
| S4 | BV remainders, ALL carriers, level **QD** (Q = ∏_{p<w₀}p const) | 0.0008 | x/log¹⁰x; vanishes |
| S5 | hyp-(4) threshold guard (w₀; no direct M-cost) | 0.0004 | see the C1d card |
| S6 | V↔U_N conversions ((114)/(115) factors) | 0.0006 | o(1) |
| S7 | thresholds/drifts: 2N^{7/8}+N^{1/3}, PNT residuals, s-drifts, prime powers, ε'-retreat 4.2e−5 | 0.0011 | o(1)/const |
| | **TOTAL 0.0121 = 57.1% of M; reserve 42.9%** | | |

Carrier-normalization convention (gate F6): the absolute carriers are
`(·)·Π₂x/(4 log z)` (|A| ≈ x/2 folded); the sensitivity ledger is
relative and unaffected; C5 pins the convention.

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
  `a_n = 1_{[x/2+2,x]}·Σ 1_{n=p₁p₂p₃}` (`z≤p₁≤y<p₂≤p₃`); level-D*
  distribution via GENERAL BV for triple convolutions of
  primes-in-intervals with an SW-regular factor; **upper sieve on
  `P(y)` at `s = log D*/log y → 3/2⁻`** (⚠️ catch #23: NOT Tao's
  `s = 1+ε` tuning, which sifts P(√x) and is irreconcilable with the
  `d ∣ P(y)` remainder freeze — the mixed form's margin is NEGATIVE;
  BJS's `½S(B,P(y))` tuning is the freeze, endpoint constant
  identical since F(s)·V(z_sift) is tuning-invariant); PNT
  double-integral count ⇒ `≤ (c̄ + o(1))·Π₂·x/(4 log z)`.
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
cluster in disguise, D-adjacent).

⚠️ **Hypothesis (4) — CORRECTED (catch #22, two gate lenses
independently):** (4) is **FALSE for the twin `g(p) = 1/(p−1)` with
ℚ = ∅** (at u = 3 the window product carries the constant
`1/Π₂ ≈ 1.515` excess — violated 1.47×, no Mertens error term can
save it; the small-u excess `∏(1−1/(p−1)²)⁻¹` must be EXCLUDED). BJS
themselves verify (4) only on `u₀ ≤ u < z` with **ℚ := {p < u₀}**,
`u₀ = 10⁹`, `ε = 1.452·10⁻⁷` (their Lemma 18; Thm 44 couples
u₀ ↔ ε). The freeze: `ℚ = {p < w₀}` with `w₀` explicit per the C1d
card; the constant `Q = ∏_{p<w₀} p` is PAID into the remainder range
`d < QD` — C2a/C3a consume the BV input at level `QD` (free
asymptotically since Q is constant, but it must be THREADED). PM1
serves ONLY the C2b q-sum grids — NOT hypothesis (4); the (4)
discharge is a product-form explicit-Mertens node (BJS Lemmas 15–18
lineage), C1d re-specced below.

**Known errata (transcribe-time traps):** Nathanson Thm 10.3 is
missing a factor 2 in `U_N` (BJS p. 36 fn. 4); Thm 10.2 needs the
`q ∤ N` side condition (BJS fn. 3); Yamada arXiv:1511.03409 is BROKEN
at (87)/(104) — never consult; Tao's lower-bound half (his (13)) is
Exercise 10 — BJS Thm 6 is the proved source for BOTH sides;
⚠️ **catch #24, an erratum in BJS v6 ITSELF (not in their errata
note): printed eq. (14) (p. 6) sums over n ODD — same parity as (13)
— forcing `F + f ≡ 2`, contradicting their (8) (`F(2)+f(2) = e^γ ≠
2`) and `f(2) = 0`. The correct definition is `f(s) = 1 − Σ_{n EVEN}
fₙ(s)` (gate-verified: series = the DDE closed forms to 1e-8 iff
even). C1a/C1c MUST define f with the even-n sum.**

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
| C0 ✅ | the margin budget ledger — FROZEN above (gate-corrected: ε_sieve = 1/10000, seven sites, 57.1% spent / 42.9% reserve) | B (done at the gate) |
| C1a ✅ | LANDED FULL (RosserChain.lean, 463 lines): `fseq` ((15)–(17), total, junk-zero windows documented; improper tails = finite intervalIntegrals via `fseq_eq_zero_of_ge`), `Fchain`/`fchain` at the #24-CORRECTED parities + the regression witness (`Fchain 1 2 + fchain 1 2 = 5/2 ≠ 2`), `fseq_two_window` = BJS (19) exactly (the gate's spot-check anchor), and the FULL integrability package by one coupled induction (measurable ∧ bounded ∧ intervalIntegrable — the risk item, closed) | B/C |
| C1b ✅ | LANDED (Tail.lean): the full BJS-Lemma-8 mechanism with an EXPONENTIAL majorant `hbar` swapped for BJS's `3s⁻¹e⁻ˢ` (makes the majorant integral elementary — dodges E₁); `fseq_le` (per-level `2e²·(99/100)ⁿ·hbar s`, one induction through (16)/(17)), `fseq_tail_le` (≤ 43/100000 uniformly on s ≥ 4/3), `fchain_close`/`Fchain_close` (the C1c consumables). ⚠️ N-FLOOR: certified ratio 99/100 (not BJS's sharp 0.9607) ⇒ **N = 2048**, not the ledger row's 23 — fine for the CLOSENESS/tail purpose (the value 4.3e−4 holds) | C |
| C1b′ | **the VALUE certification** (needed by C5 assembly, NOT by C1c): certified numeric lower bounds on `fchain N 4` (and the F-values on [4/3, 3]) — at ρ = 99/100 the tail forces ~1000 level evaluations (infeasible); the route is Table-2-sharp per-level `cₙ` for n ≤ ~25 (each a one-integration bound in the `fseq_two_window` style) + the sharp tail. Dispatch AFTER C1c fixes the exact consumption shape | C (compute-heavy) |
| C1c ◑ | **BJS Theorem 6** — EXCEEDS floor B (LinearSieve.lean, 589 lines): the generic `TruncSieve` engine (the B2 peel machinery generalized from `chi` to abstract predicates — pointwise ± proved ONCE), the GENUINE Rosser positional predicate `rosserCond` with divisor-closure via a new sorted-sublist positional-domination lemma (`rosserCond_dvd_closed` — mathlib lacked it) + parity closure, `rosserSieve_isUpper/LowerMoebius` (**the Rosser–Iwaniec fundamental sieve inequality, first anywhere**), the full assembly `linear_sieve_upper/lower` with the `d < QD` remainder, and the BJS (5)/(6) chain packaging (`W·(Fchain/fchain ± εCᵢe²·hBJS)`, ε/Cᵢ parametric). Remaining = **C1c′**: the main-term comparison `hmain` (BJS Prop 13/Lemma 11 — the Tₙ Buchstab-chain induction coupling fₙ/h/H to the prime sums via hyp (4), the τₙ bookkeeping) + the support bound `hsupp` (`rosserCond → d < QD`; the lower ν=2, r=1 case needs `p < z ≤ √D` — the honest home of the D ≥ z vs D ≥ z² asymmetry). STOP-AND-FLAG check ✓: nothing outside the frozen set | C+ (keystone 1) |
| C1c′ ✅ | `hsupp` FULL both sides (Buchstab.lean: `support_core` — the honest D ≥ z vs z² asymmetry home) + catch #25 (the lower hsupp unsatisfiability, fixed at source) + the Buchstab base/defect + compiler-plugged endpoints | C+ |
| C1c″ ✅ | **the Buchstab decomposition = BJS Prop 13 EXACTLY** (TnInduction.lean, 827 lines, 46 lemmas): `buchstab_upper/lower` (`mainSum λ± = W ± Σ_{parity} Tₙ`, an IDENTITY, sign-audited; via `buchstab_defect` — first-violation fiber decomposition, both fiber directions proved) + `hmain_upper/lower` (the exact `hmain` plugs, single named hypothesis `hTbound`) + the `hbar_le_hBJS` bridge + `linear_sieve_*_rosser_assembled` (compiler-verified BJS Thm 6 (5)/(6) modulo `hTbound`). Reusable: `rlist_mul_block`, prefix/suffix split, `Vbelow_eq` | C+ |
| C1c‴ ◑ | floor A (Lemma11.lean, 510 lines): **n = 1 FULL** — `T_one_upper` an EXACT Buchstab identity via the new reusable `prod_telescope` (Σ aₚ∏_{q<p}(1−a_q) = 1 − ∏(1−aₚ); mathlib lacked it); `hlevel_one_upper` at τ₁ = 3 (⚠️ FINDING: the per-level close MUST run against hBJS, not hbar — `1/s ≤ e²·hbar` FAILS at s → 3⁻; C1c″'s `hbar_le_hBJS` slack is load-bearing exactly there); `T_two_one_zero`; **Lemma-12 τ-close PARAMETRIC** (`tau_sum_le_of_recursion`, uniform-in-M); the `_final` assemblies close BJS Thm 6 modulo `hlevel` (n ≥ 2) + `htau`. At N = maxDepth the truncation is EXACT — no fseq-tail slack spent | C+ |
| C1c⁗ ✅→#27 | (superseded by C1c⁶'s re-keyed skeleton for the hstep path; the peel identity + everything combinatorial stands) — original row: ◑ | **discharge `hlevel` (n ≥ 2)**: (i) the restricted sieve `sieveBelow s p` + the peeling identity `Tₙ(D,z) = Σ_p ν(p)·T_{n−1}(D/p, p)` (T bakes z into prodPrimes — the infrastructure gap); (ii) the (34)/(35)–(38) induction (Tail.lean's `hbar_funcbound` is the template, closed against hBJS); (iii) BJS's exact (31) constants (γ₃/κ₃/cₙ) at page-image level → the frozen-row C₁ = 106/C₂ = 108 instantiation of `htau` | C+ |
| C1d ✅ | LANDED FULL (Hyp4.lean): `vratio_prod_le` (parametric ε, abstract threshold; PM1 C₃ = 19 + the new `neg_log_nu_le` (−log(1−x) ≤ 1/p + 4/p² at x ≤ 1/(p−1), p ≥ 3 — the p = 3 panel via log 2 ≤ 7/9) + the 4/(u−1) telescope), `h4_base` (Lemma11's exact h4 slot at K = 1+ε), `vratio_window_le` (the hstep' feed), `w0R ε = exp(40/log(1+ε))` explicit (23/40-share arithmetic; ≈ e^{4·10⁵} at the frozen row), `thresh_mono`, `Qval` exported for C2a's d < QD. Chen's density CONFIRMED dimension-1 (ν(p) = 1/(p−1), the {−2 mod p} residue). C2a supplies hcube/hlogrel/the concrete ν-bound at instantiation. Original spec (catch #22): `ℚ = {p < w₀}`, `w₀ := exp(19/(share·log(1+ε_sieve)))`-shape (≈ e^{3.8·10⁵} at 1/10000, half-share) OR port BJS Lemma 18 verbatim (u₀ = 10⁹, their ε = 1.452·10⁻⁷ — then re-freeze ε_sieve to match, Fable decision at dispatch); product-form explicit Mertens on `u ∈ [w₀, z)` (a real C node); NEW pointwise helper `−log(1−1/(p−1)) ≤ 1/p + 4/p²` (p ≥ 3) wanted; do NOT consume `neg_log_one_sub_nu_le` (2/p, BoundingSieve-typed); export `Q = ∏_{p<w₀}p` as the level constant | C |
| C2a ✅ | LANDED FULL (TwinA1.lean): `twinA1Sieve` (the shifted-single BoundingSieve at ν = 1/φ(d) — totient form makes multiplicativity immediate; ν = BV-main-term match EXACT), the pointwise (39) reduction `twinA1_abs_rem_le` (two-endpoint subtraction PROVEN, ψ_{χ₀}↔ψ conversion PROVEN via BV.norm_psiChi_one_sub_psiTot_le, even-d branch DISSOLVED by the ℚ-window), sieve-class facts proven (hnu tight, hguard from w0R), the assembly `twin_A1_lower` (BJS (6) with the per-step comparison DISCHARGED, fchain symbolic, level Q·D threaded). Named-parametric: h4-family, hτrec/htau (C1cτ), and `hBV` (the summed remainder ≤ x/log¹⁰x — the L¹ sum over d ∣ P < QD + the two-endpoint BV at the unconditional gate + absorptions = node **C2c**) | C |
| C2c | discharge `hBV`: the L¹ remainder sum — Σ_{d ∣ P, d < QD} of the pointwise bound (C2a's `twinA1_abs_rem_le`) via the UNCONDITIONAL `psi_BV_of_siegelWalfisz'` + `siegelWalfisz_holds` at the two endpoints (the level QD ≤ √x/(log x)^B check at Q constant), + the ω(d)log/φ(d) conversion sum (crude divisor bounds) | C |
| C2b ✅ | LANDED FULL (TwinA2.lean): `twin_A2_per_prime` (keystone per restricted sub-sieve, abstract-family — the p ∣ n+2 restriction never touches the sieve), `A2grid` symbolic + `A2grid_le_envelope` (sup·mass via PM1; the pieces refinement NOT needed — S2 headroom covers), `twin_A2_upper` (C5 packaging; hcoef/hBVagg named for C5 reconciliation) | C |
| C3a | **general BV, weak form** (fixed scale/residue, L¹, SW-hypothesis-named) — Vaughan + large sieve + dispersion pipeline reuse | C+ (keystone 2) |
| C3b | β-SW: the interval prime-indicator derivation from the gate | C |
| C3c | the fine-partition bookkeeping (λ = 1+log^{−20}x blocks, diagonal absorption, explicit-K budgets per the DispersionClose precedent) | C |
| C3d | the count of `Σa_n` — ⚠️ DESIGN NOTE (from C4a's floor): the Lean shape will bound the triple-prime count by EXPLICIT prime sums (PNT-with-error / mathlib's upstreamed PNT — hunt what error term is now available), NOT by the smooth integral `cbar`; spec C3d's endpoint against the LITERAL 0.363084-ledger line (C4a's `two_log_three_sub_log_six_sub_cbar_pos`), so `cbar_lt` (deferred, dilog-blocked) is never consumed. The S7 cap (0.0011 abs) prices the PNT residual — Chebyshev-only bounds (38% slack) canNOT serve; a genuine PNT error term is REQUIRED here | C |
| C4a ◐ | FLOOR landed (SwitchConstant.lean): `cbar` def + `cbar_pos` + **`two_log_three_sub_log_six_sub_cbar_pos`** (the only line C5 consumes: `log(3/2) ≥ 2/5 > 0.363084`). `cbar_lt` DEFERRED — the 2.7e−7 gap is beyond elementary majorants (concave integrand ⇒ tangent lines optimal ⇒ ≳220 panels each carrying a `log(rational)`; no norm_num log extension) and mathlib has NO Li₂/polylog (the exact dilog route needs a from-scratch dilog library, C+, separate session). Likely never needed if C3d follows its design note | B (floored) |
| C4b | prime-power strip (½Σ1_{p²∣n+2} WITH the coprimality restriction) + the `x^{2/3}` validity threshold of the weights + the Lemma-37 `2N^{7/8}+N^{1/3}` losses | A/B |
| C5 | assembly → **`chen_of_siegelWalfisz`** | C |

PB-floors: C1c alone is a standalone mathlib-first artifact (the first
formal Rosser–Iwaniec linear sieve); C3a alone upgrades the BV corpus
to convolutions (serves any future E₂/E₃ work); if the razor assembly
stalls, the floor is `p + 2 = P₄`-shape at the same architecture with
slack margins (state honestly, flag). The optimality/parity section of
BJS stays OUT (not needed).

## C1cσ — the decaying per-level constants (specced 2026-07-13, after C1cτ's findings)

C1cτ PROVED (machine-checked) that the numeric τ-row cannot close
against the landed cf_const/ch_const: (catch #29) the global hτrec is
unsatisfiable at n = 0 (the induction only uses n ≥ 1 — the one-token
amendment); and (the wall) ch_const = (1+ε)Cabs(n+3)e^{n+3} never
contracts ⇒ achievable C₁' ≥ 3·2^{π(z)}; no ε-refreeze helps. ROOT
CAUSE + FIX (Fable): the sup-envelope endgames of hf_of_window/
hh_of_window used `fseq_le_two`/worst-case-window conversions,
THROWING AWAY the landed geometric decay — `fseq_le : fseq (n+1) s ≤
2e²(99/100)ⁿ·hbar s` (Tail.lean) gives the per-level sup a FREE rⁿ
factor. C1cσ = re-run the two comparison endgames carrying the
geometric factor: c_f(n), c_h(n) ≤ K·(99/100)ⁿ-shape ⇒ the τ-recursion
contracts ⇒ tau_sum_le_of_recursion closes at explicit C₁'/C₂';
re-check the C0 ledger at the achieved constants (the S-row slack
scales by C₁'/106 — the gate showed 1.8× headroom at 106; if C₁' >
~200, re-freeze ε_sieve at the pre-verified 1/100000 row for 10×
more headroom). Deliverables: the n≥1 hτrec amendment (prime-form
consumers alongside the landed ones), cf_dec/ch_dec + the amended
comparisons, tauChenσ + the geometric close, the ledger check.

## Pre-dispatch gates — ALL CLEARED 2026-07-12
1. ✅ page-image transcription (dossier in the session scratchpad;
   recon confirmed at pixel level).
2. ✅ C0 ledger — frozen above (gate-corrected).
3. ✅ the adversarial gate workflow (4 lenses: 2 BLOCK + 2
   PASS_WITH_CORRECTIONS → catches #21–#24 folded into this
   revision). The c̄ certificate verified 3-way independently
   (tanh-sinh / Simpson / closed dilog form — the dilog route is
   C4a's recommended exact-arithmetic path: `c̄ = [log2·logβ −
   Li₂(3β/2)] + [log3·logu + (logu)²/2 + Li₂(1/(3u))]` at the
   endpoints).
Wave 1 = C1a + C1b + C4a (C0 done; the corrected even-n f-definition
and the ε_sieve = 1/10000 certification targets are BINDING).
