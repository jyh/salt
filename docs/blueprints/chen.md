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

**C0 AMENDMENT 1 (Fable, 2026-07-13, on E₁b's arithmetic): `ε_sieve`
RE-FROZEN `1/10000 → 10⁻⁷`.** Driver: the achieved sharp constants are
`C₁′ = C₂′ = Csharp ≤ 15074` (`TauSharp.Csharp_frozen`; → 15000 as
ε → 0), not BJS Table 1's 106/108 — the elementary route to those is
kernel-proven impossible (catches #29/#30), and the τ-relative route's
`Csharp` is bounded in ε, so the refreeze closes. At `ε = 10⁻⁷`,
`C′ = 15074`: S1 spend 1.53e−4 (cap 0.0022, 14.4×), S2 spend 1.06e−3
(cap 0.0055, 5.2×), S3 spend 6.35e−4 (cap 0.0015, 2.4× — S3 BINDS,
threshold ε ≤ 2.4e−7). Caps UNCHANGED (spends shrink; total spend on
S1–S3 drops 0.0092 → 0.0018). Downstream: `Hyp4.w0R` is parametric —
`w0R(10⁻⁷) ≈ exp(4·10⁸)`, still a constant (fine for `Infinite`);
every `(1+ε)` site improves; no landed node relands. Verified
independently (Fable re-derivation) against the executor's table.

**C0 AMENDMENT 3 (Fable, 2026-07-13, RATIFIED at E₁c-close):
`ε_sieve = 2·10⁻⁸`** (supersedes Amendment 1's 10⁻⁷). Driver: the
gate-corrected sharp-B constants (CsharpB ≤ 100001). Rows verified
twice independently (the E₁c freeze gate's envelope lens + fidelity
lens): S1 spend 2.03e−4 (10.8×), S2 1.40e−3 (3.9×), S3 8.42e−4
(1.78×, binds). w0R(2e−8) ≈ exp(2·10⁹), a constant. All landed
sharp-B lemmas carry ε-hypotheses satisfied at 2e−8 (0 ≤ ε ≤ 1/1000,
ε < 1/249 derived). The H-glue instantiates this value.

**C0 AMENDMENT 2 (Fable, 2026-07-13, on C1b″'s arithmetic; catch
#31): `ε′` FROZEN `= 10⁻⁴`; the A₁ value-certification interval is
the 8ε′-window `[4 − 8ε′, 4] = [3.9992, 4]`, NOT `[39/10, 4]`.**
The C0 prose said "keep ε′ ≈ 1/200" while the S7 line item
"ε′-retreat 4.2e−5" was computed at ε′ = 10⁻⁴ (retreat =
f′(4)·8ε′, f′(4) = 2e^γ(1/12 − log3/16) ≈ 0.05226: at 10⁻⁴ →
4.18e−5 ✓; at 1/200 → 2.1e−3, exceeding S7's ENTIRE cap 0.0011).
The arithmetic governs: ε′ = 10⁻⁴. Consequence (C1b″'s finding):
the A₁ target `fchain ≥ 0.9779` is unreachable uniformly on
[39/10, 4] (true fchain(3.9) = 0.9725) but the demand only ever
lives on the 8ε′-window, where the true even-sum is ≤ 0.021646 +
4.2e−5 = 0.021688 vs the 0.0221 target — headroom 4.1e−4 (1.9%
rel), feasible for a fine-knot piecewise-linear cascade. D =
x^{1/2−ε′} at 10⁻⁴ still sits under the general-BV level (S4
unaffected). A₂ unchanged: odd-sum ≤ 1.68 on [4/3, 3] (true sup
1.6716, 0.5% headroom).

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
| C1b′ ◑ | **the VALUE certification** (needed by C5 assembly, NOT by C1c): certified numeric lower bounds on `fchain N 4` (and the F-values on [4/3, 3]) — at ρ = 99/100 the tail forces ~1000 level evaluations (infeasible); the route is Table-2-sharp per-level `cₙ` for n ≤ ~25 (each a one-integration bound in the `fseq_two_window` style) + the sharp tail. Dispatch AFTER C1c fixes the exact consumption shape. **PARTIAL** (ChainValues.lean): interface in exact C5 shapes (`fchain_lower_of_evenSum_le`/`Fchain_upper_of_oddSum_le` + depth-monotonicity), the genuine sharp LEADING per-level bound `fseq_two_le_sq` (`f₂ ≤ (4−s)²/(s(s−1)) ≤ 1/1000`, the `fseq_two_window` template), the SHARP tail `fchain_trunc_close` (reuses C1b `fseq_tail_le`; `fchain N ∈ [fchain 2048 − 4.3e−4, fchain 2048]`), and `chen_ledger_line`. REMAINING = the sharp head (even n ≤ ~2048): the decaying-cₙ cascade = **C1cσ** (see flags 2026-07-13 C1b′; the landed `fseq_le` ρ=99/100 provably gives NO positive lower bound, ledger needs fchain ≥ 0.9779 / supF ≤ 2.68) | C (compute-heavy) |
| C1b″ ◑ | **the cascade engine + the design verdict** (ValueCascade.lean, floor B): `fseq_next_le_of_shift_majorant` (the general per-level step: `fseq n ≤ g on [lo,up]` ⇒ `fseq (n+1) s ≤ (1/s)∫g`, keyed on the window equations — serves even/odd-tail/odd-flat uniformly), `integral_M3` (exact partial-fractions antiderivative), `fseq_three_tail_le`/`fseq_three_flat_le` (the first genuine level past f₂, both regions). VERDICT (kernel-adjacent numerics, matches C1b′'s table): closed-form majorants are 2.3–3.1× loose PER LEVEL (log-linearization) ⇒ provably non-load-bearing at ≤0.5% headroom; the load-bearing route is fine-knot PIECEWISE-LINEAR majorants with exact per-panel integrals feeding the engine. A₁ interval catch → C0 Amendment 2 (catch #31). The PL cascade = the final C1cσ artifact | C (compute-heavy) |
| VC2 ◑ | **floor A** (PLCascade.lean): the self-certified geometric-tail pipeline in the exact A₁ interface shape (head + geometric tail keyed on a two-level contraction; certified end-to-end demo at r = (99/100)²), PL glue lemmas (rational, log-free panels). Targets confirmed TRUE; closure re-scoped: the pointwise two-level ratio blows up at the right support edge (no invariant profile ⇒ no cheap contraction), ~10³ panels/level at A₁ tightness ⇒ **C1cσ is a multi-session keystone**. NEW: **A₂ ⟺ Σ even masses ≤ 0.5733** (true 0.5623, 2% slack, scalars, no edge pathology) — the mass ledger is the keystone's attack surface | C → keystone |
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
| C3c ◑ | the fine-partition bookkeeping (λ = 1+log^{−20}x blocks, diagonal absorption, explicit-K budgets per the DispersionClose precedent). PARTIAL (ConductorDescent.lean): the **count→twist duality bridge FULL** (`bilinTwist_le_of_classDisc` — dual of C3a's χ-orthogonality, over `(ℤ/d)ˣ`) + **`hβSW_of_prime_indicator` FULL** (C3b count-form → C3a twist-form for `blockPrimeInd`) + **`general_BV_closed` FULL** (`general_BV_weak` with `hβSW` DISCHARGED; keystone 2 closed for the prime indicator modulo `‖α‖≤1`, scale-compat, and `hLargeDisc`). REMAINING: the bilinear conductor descent `hLargeDisc` (the α-side primitive-reduction obstruction — see flags 2026-07-13 C3c; the linear V3.1 descent does not mirror to the product) | C |
| C3d | the count of `Σa_n` — ⚠️ DESIGN NOTE (from C4a's floor): the Lean shape will bound the triple-prime count by EXPLICIT prime sums (PNT-with-error / mathlib's upstreamed PNT — hunt what error term is now available), NOT by the smooth integral `cbar`; spec C3d's endpoint against the LITERAL 0.363084-ledger line (C4a's `two_log_three_sub_log_six_sub_cbar_pos`), so `cbar_lt` (deferred, dilog-blocked) is never consumed. The S7 cap (0.0011 abs) prices the PNT residual — Chebyshev-only bounds (38% slack) canNOT serve; a genuine PNT error term is REQUIRED here | C |
| C4a ◐ | FLOOR landed (SwitchConstant.lean): `cbar` def + `cbar_pos` + **`two_log_three_sub_log_six_sub_cbar_pos`** (the only line C5 consumes: `log(3/2) ≥ 2/5 > 0.363084`). `cbar_lt` DEFERRED — the 2.7e−7 gap is beyond elementary majorants (concave integrand ⇒ tangent lines optimal ⇒ ≳220 panels each carrying a `log(rational)`; no norm_num log extension) and mathlib has NO Li₂/polylog (the exact dilog route needs a from-scratch dilog library, C+, separate session). Likely never needed if C3d follows its design note | B (floored) |
| C4b ✅ | LANDED FULL + the Lemma-11 casework (WeightTrivia.lean): the P₂ carrier `IsP2 z m` (prime ∨ semiprime both factors ≥ z — Tao's native form), `chen_weight_le_indicator` + `chen_weight_struct` (the FULL weight inequality: ¬IsP2 ⇒ Ω ≥ 3 ⇒ the ω-casework with the `large_mult_le_two` size lemma — C5 gets `chenWeight ≤ p2Ind` unconditionally on the window), `stripSum_le` (the coprimality-cut strip ≤ x·log x/(z−1) ≈ x^{7/8}log x), `window_two_thirds_lt` (validity automatic), `switch_loss_le` (the S7 bookkeeping) | A/B |
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

## E₁-dev (USER-RATIFIED 2026-07-13 morning) — the sharp τ-numerics

Two nodes closing the last numeric debt (the elementary route being
kernel-proven impossible, catches #29/#30):
**E₁a** — the sharp funcbound: `hBJS_funcbound_sharp : ∫_{s−1}^{c}
hBJS ≤ (49/50)·s·hBJS s` on the operating window — via the
parts-twice bound `∫_3^∞ 3u⁻¹e⁻ᵘ ≤ (8/9)e⁻³` (C1c⁶'s worked route:
∫ = 3a⁻¹e⁻ᵃ − 3∫u⁻²e⁻ᵘ and ∫_a^∞ u⁻²e⁻ᵘ ≥ a⁻²e⁻ᵃ(1−2/a)); no full
E₁ library needed — the finite certified integrals suffice.
**E₁b** — the BJS-(31)–(39)-faithful per-level bookkeeping: the
τ-RELATIVE formulation (their hₙ = ετₙe²h(s) with the (35)–(38)
four-way split producing τₙ₊₁ from κ₃-contraction + geometrically-
decaying forcing — the f-side must ALSO be τ-relative; our landed
absolute cf_const(n)·e^{n+3} growth is exactly what the relative
form avoids), the concrete tauSharp with Στ-odd/even ≤ explicit
C₁′/C₂′, the C0 ledger check at the achieved constants (1.8× headroom
at 106/108; the 1/100000 ε-refreeze row pre-verified for 10× more),
and the instantiation into bjs_theorem6_windowed's hτrec (n ≥ 1 per
catch #29)/htau slots → twin_A1_lower/A2's parametric debts CLOSED.

**E₁a ✅ LANDED** (`SharpFuncbound.lean`): `hBJS_funcbound_sharp`,
κ₃ = 49/50 via the parts-twice Gtail route; the tail bound is
load-bearing at 0.24% margin; threshold s₀ = 2.
**E₁b ✅ LANDED** (`TauSharp.lean`, Floor A+): the τ-relative
machinery in full — `cfSharp = 3εe²rf^n` (the ε-cancellation:
forcing/τ-unit = 3·(99/100)^n, ε-FREE), `chSharp = (1+ε)(49/50) < 1`,
`tauSharp` with the global `hτrec` DISCHARGED (dissolves catch #29:
equality at every n, `cfSharp 0 ε = 3εe² = εe²τ₁` exactly),
`Σodd/even ≤ Csharp ε ≤ 15074`, E₁a consumed (`sharp_h_contract`),
parametric consumers `bjs_theorem6_sharp_{upper,lower}` with hτrec AND
htau both discharged. THE LEDGER CLOSES → C0 Amendment 1 (ε_sieve =
10⁻⁷). NOT in this node (flagged, above Opus tier — the remaining
E₁-dev queue):
**E₁c** (C, own session) — the sharp discrete→integral pushforward:
`Σ_p (1/(p−1))(log z/log p)h(σ_p) ≤ (1/s)∫_{s−1}h`-shape with
s-dependent error control, producing the `hf`/`hh` slots at
(cfSharp, chSharp); the landed `decay_mass_le` keeps only the absolute
`Cabs`, discarding the s-dependence that E₁a's 49/50 needs.
**E₁c PRE-DESIGN NOTES (Fable, 2026-07-13, from the PIXEL-VERIFIED
BJS pp. 10–12 — the (28)–(39) proof of their Lemma 11):**
(a) BJS Thm-6/Lemma-11 does NO discrete pushforward itself: (34)
imports it from [40, Lemma 9.8] (Nathanson GTM 164 ch. 9; we don't
hold the source — Tao supp-5 / Halberstam Astérisque in the dossier
carry the same lemma; transcribe whichever at page level pre-freeze).
(35)–(38) = exactly E₁b's landed bookkeeping ((37): the f-integral is
EXACT by the recursion (16) — our window equations; (38): κ₃ = E₁a).
(b) THE ODD-FLAT BRANCH (n ≥ 3 odd, 1 ≤ s ≤ 3) uses BJS (39) with K²
and `V(D^{1/3}) ≤ (3K/s)V(z)` — their footnote 1 FIXES A KNOWN ERROR
IN NATHANSON's Thm 9.5 (his `f_n(3)+h_n(3)` claim contradicts
linear-sieve optimality). Freeze (39), never [40]'s odd-flat step.
(c) BOUNDARY-DEFECT WARNING for the freeze: (34)'s boundary terms
(35)/(36) carry `(K−1)g(s−1) ≤ ε·γ₃·g(s)`-defects (γ₃ ≈ (4/3)e ≈
3.62 for hBJS on the operating range). The E₁b-frozen `chSharp =
(1+ε)(49/50)` has only (49/50)ε of ε-room — the honest windowed
per-step likely needs `chSharpB := (1+ε)(49/50) + 4ε` (envelopes
γ₃; still < 1 at any ε < 1/300; Csharp moves by ~3e−4 at ε = 10⁻⁷ —
ledger unaffected). Thanks to E₁d's parametric keystone this is a
FREE instantiation change: E₁c should land tauSharpB/CsharpB
(~40-line TauSharp mirror at chSharpB) and discharge StepHypWP at
(cfSharp, chSharpB) — do NOT try to squeeze the boundary into E₁a's
0.24%-margin statement or the n-dependent f-slot (fails at n ≳ 180).
Similarly audit cfSharp's room against BJS's (35) f-boundary
`2γ₃(c_{n−1})^{n−2}/τ_{n−1}` — if our discrete route incurs it, the
f-forcing needs `cfSharpB ≈ 8εe²rf^n`-shape (Csharp scales by 8/3 —
still bounded in ε, ledger recheck: S-thresholds shrink 8/3× to
ε ≤ ~9e−8 at S3 — refreeze ε_sieve to 5e−8 if so; caps still hold).
FREEZE ONLY AFTER the pushforward route is worked at Lemma-9.8 level
against the landed AbelStep telescope (telescope_ge, stepHyp_lhs_eq,
Vbelow_le_ratio) — the boundary structure depends on OUR peel's exact
form, not BJS's continuous one.
(d) ROUTE REFINEMENT (Fable, corpus-grounded): the per-step reduces
via the landed `stepHyp_lhs_eq` + `ledger_collect` to TWO windowed
comparisons, both against the Stieltjes measure m_p = ν(p)·Vbelow(p)
whose (29)-control is landed (`Vbelow_le_ratio`: V(p) ≤
(1+ε)(log z/log p)·W under the hguard, i.e. K = 1+ε exactly):
• hh-sharp (`Σ m_p·hBJS(σ_p) ≤ W·chSharpB·hBJS(S)`): hBJS is
  non-increasing and σ_p is decreasing in p, so g(σ_p) is increasing
  in p and the layer-cake/up-set argument applies: {g ≥ y} is an
  up-set with mass V(t(y)) − W (`telescope_ge`), V(t)/W ≤ (1+ε)·
  (log z/log t); reconstruct ≤ (1+ε)·W·(1/S)∫_{S−1}h + the z-edge
  boundary (the (36)-defect, ε-scale) → E₁a closes at 49/50; the
  boundary rides in the +4ε pad of chSharpB.
• hf-sharp (`Σ m_p·fseq n(σ_p) ≤ W·(fseq(n+1)(S) + cfSharpB·hBJS S)`):
  fseq is NOT monotone — do NOT layer-cake it. BJS's own route: the
  main term is the EXACT recursion ((16)/our window equations:
  (1/S)∫fseq n(t−1)dt = fseq(n+1)(S) on the tail branch; windowed
  variants otherwise), so ONLY THE DEFECT needs bounding:
  |Σ m_p·fseq n(σ_p) − W·(1/S)∫fseq n| ≤ (ε-slack of the measure per
  (29) + Riemann/panel error) × ‖fseq n‖-mass, and `fseq_le`
  (2e²·rf^{n−1}·hbar) converts the mass to the geometric rf^n·h-shape
  → cfSharpB. The (35)-boundary (ε·2γ₃e²rf^{n−2}-scale) fixes
  cfSharpB ≈ 8εe²rf^n (vs E₁b's 3): re-freeze via the E₁d parametric
  layer with tauSharpB/CsharpB ≈ (8/3)·15000 = 40000; ledger recheck
  at ε = 10⁻⁷: S3 spend 8/3× = 1.7e−3 vs cap 1.5e−3 — FAILS at 10⁻⁷!
  → refreeze ε_sieve = 5·10⁻⁸ alongside (S3 spend 8.4e−4, margin
  1.8×; S1/S2 comfortable; w0R(5e−8) ≈ exp(8·10⁸) still a constant).
  PRE-VERIFY this pair (cfSharpB envelope + ε = 5e−8) numerically at
  gate time BEFORE freezing; the odd-flat branch (BJS (39), K²-terms)
  may add its own envelope constant — audit it in the same gate.
(g) **FREEZE V2 (Fable 2026-07-13, post-gate — THE frozen design):**
KEY STRUCTURAL RESOLUTION: our discrete `T_peel` ALREADY encodes BJS
(39)'s restriction — the `p³ < D'` side-1 filter forces σ_child ≥ 2
(logRatio_child_lower), which is BJS's `V(D^{1/3})` in discrete form.
So NO new induction branch: the odd-flat case is the flat-window
branch of the comparison proofs (fseq_odd_flat_window + the landed
E₁a-flat). The fix is the CONDITIONED CONTRACT:
1. `StepHypWPC (cf ch : ℕ → ℝ) (ε) (tau)` = StepHypWP + TWO premises:
   `loBnd side' ≤ logRatio z D'` and the PARITY COUPLING
   `side' % 2 ≠ n % 2` (per-step child-depth form; parent form
   `side' % 2 = depth % 2`). The descent preserves the coupling
   (side and depth flip together); the keystones' top calls satisfy
   it (upper sums odd depths at side 1, lower even at side 2); the
   excluded base (side 2, depth 1) was `T_two_one_zero = 0` anyway.
   StepHypWP → StepHypWPC trivially (more premises), so the const
   instance is free.
2. `T_le_of_peel_step_wpc`: the E₁d induction with the invariant
   `side' % 2 = n % 2` threaded (hlow already is); conditioned
   `hlevel_wpc_*`, keystones `bjs_theorem6_windowed_c_{upper,lower}`.
   Verify hTbound_{upper,lower}_of_levels consume hlevel ONLY at the
   coupled parities (odd@1 / even@2) — expected from the htau
   filters; if not, STOP AND FLAG.
3. B-mirror per the gate: `cfSharpB n ε = if n = 0 then 3εe² else
   20εe²(99/100)ⁿ`; `chSharpB ε = (1+ε)(49/50) + 4ε`; `tauSharpB`
   (hτrec case-split n=0 anchor 3 ≤ 20 / n ≥ 1 equality); `CsharpB =
   2000/(1−chSharpB) ≤ 100001` concrete; contraction hypothesis
   `ε < 1/249` (NEVER hε49); sums both parities.
4. B-plugs: the conditioned keystones at (cfSharpB, chSharpB,
   tauSharpB, CsharpB), leaving `hstepWPC-B : StepHypWPC (cfSharpB ·)
   (fun _ => chSharpB ε) ε (tauSharpB ε)` as the single analytic slot.
5. The analytic discharge (2 nodes after E₁d′): **E₁c-hh** (layer-cake
   on the descending-V measure: telescope_ge + Vbelow_le_ratio;
   E₁a on σ ≥ 2 cells, E₁a-flat on the odd-flat cells; γ₃ʰ ≤ 4
   boundary in the +4ε pad; gate-verified to close at 0.9607/0.9214)
   and **E₁c-hf** (window recursions exact on the main term:
   even-window/odd-tail/odd-flat forms; defect via fseq_le geometric;
   needs helper `fseq_antitoneOn [loBnd(parity), ∞)` — numerically
   verified twice). Then **E₁c-close**: ledger_collect composition →
   discharge the slot → C0 AMENDMENT 3 (ε_sieve = 2·10⁻⁸) ratifies.
(f) **THE FREEZE GATE RAN 2026-07-13 — BLOCK (catches #32/#33, see
flags). FREEZE V2 REQUIRED before any dispatch:**
1. `StepHypWPC` — the CONDITIONED contract: StepHypWP + the loBnd
   invariant `loBnd side' ≤ logRatio z D'` (the induction already
   threads it as hlow). The unconditioned StepHypWP is PROVEN
   undischargeable at ε-order coefficients (catch #32 counterexample).
2. The sharp windowed induction `T_le_of_peel_step_wb` gets a THIRD
   branch: the BJS-(39) REROUTE, taken exactly where the naive peel
   would evaluate even-index fseq below 2 (the odd-flat regime); new
   step lemma bounding T via the `V(D^{1/3}) ≤ (3K/s)V(z)` mass at
   fixed arguments (f at 2, ∫_3^∞). BJS never peels naively there;
   neither can we at sharp constants.
3. **E₁a-flat** (new lemma, catch #33): `∫_3^∞ hBJS(t−1)dt ≤
   (97/100)·s·hBJS s` on `1 ≤ s ≤ 3` (E₁a is s ≥ 2 only; the
   odd-flat h-side needs the κ̃-analog; 1.1% margin at s = 1 via the
   existing parts-twice tail bound; 97/100 < 49/50 keeps chSharpB).
4. B-mirror hypotheses: contraction needs `ε < 1/249` (NOT hε49);
   B-hτrec needs the n = 0/n ≥ 1 case split (anchor 3 ≤ 20 vs
   equality).
5. Envelopes/ledger INDEPENDENTLY CONFIRMED (gate): γ̄ = 3.0369,
   γ₃ʰ = 3.6244 global; cfSharpB = 20εe²rf^n has ~2.5× honest
   cushion; ε_sieve = 2e−8 rows verified (S3 binds 1.78×).
6. H-glue note: TwinA1/A2 wire the ABSOLUTE keystones today; the
   sharp chain rewires them to the B-plugs.
(e) ENVELOPE PRE-VERIFICATION (Fable 2026-07-13, against the LANDED
lemma forms — supersedes (d)'s guesses):
`hbar_le_hBJS` is uniform constant-1 (hbar rate 6/5 > 1) — NO (n+3)
reintroduction; `fseq_le` converts freely to hBJS units. Boundary
ratios (computed from the landed hbar/hBJS branch forms):
γ̄ = sup_S hbar(S−1)/hBJS(S) = (5/3)e^{3/5} ≈ 3.04 at S = 5 (≤ 3.1);
γ₃ʰ = sup_S hBJS(S−1)/hBJS(S) = (4/3)e ≈ 3.63 at S = 4 (≤ 4).
f-side rows (in εe²·hBJS(S) units): K-excess 2rfⁿ; z-edge boundary
2γ̄/rf·rfⁿ ≈ 6.3rfⁿ; ODD-FLAT (BJS (39)) dominates: 3K(K−1)f-edge ≈
6e/rf·rfⁿ ≈ 16.5rfⁿ + K²-excess ≈ 2rfⁿ. CANDIDATE FREEZE:
**cfSharpB = 20·ε·e²·rfⁿ, chSharpB = (1+ε)(49/50) + 4ε**, giving
CsharpB = 2000/(1−chSharpB) → 100000 as ε → 0. LEDGER (C0 Amendment 3
candidate): **ε_sieve = 2·10⁻⁸** — S3 spend 8.4e−4 (cap 0.0015,
1.8×), S2 1.40e−3 (cap 0.0055, 3.9×), S1 2.0e−4 (cap 0.0022, 10.8×);
w0R(2e−8) ≈ exp(2·10⁹), still a constant. ROUTE ENABLER to check:
`fseq_antitoneOn` (each fseq n antitone on [loBnd(parity), ∞) — the
below-window junk-zeros sit LEFT of loBnd and the windowed peel never
evaluates there) — if true (numeric check running), ONE layer-cake/
Abel engine serves both hf and hh; if false, the f-side needs the
piecewise-monotone split. GATE: verify all of the above independently
(different method) before the freeze; then decompose into executor
nodes (engine / hh / hf-3-branches / composition+TauSharpB mirror).
**E₁d** (Fable-tier design) — parametrize `WindowedStep`'s hardcoded
`cf_const`/`ch_const` over `(cf, ch)` so the sharp coefficients reach
the REAL A₁ operating point s ≈ 4 (the unwindowed consumers landed in
E₁b carry `hσ3 : σ ≤ 3`, false at s = 4).

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
