# The conjectural landscape: EH, RH, Siegel zeros — why the hypotheses stay hypotheses

*Fable, 2026-07-12. User-ratified deliverable joining `parity-frontier.md` on the
roadmap/writeup shelf. Sourced recon with sources open: eleven scouts (EH history,
BV/FI/BFI, the modern beyond-1/2 landscape, structural blockers, conditional
status + GEH, mathlib distance, RH status, RH strategies/blockers, Siegel
structure/ladder, Siegel consequences/eliminations) plus direct primary fetches
(Goldfeld-proof exposition read page-by-page; Granville–Stark and Tao–Teräväinen
PDFs; mathlib source at this repo's pin). Every corpus claim verified against
source files this session. Precision guards at the end — this memo will be
quoted, and secondary-only claims are flagged there. All eleven briefs are
folded in, including the EH-history/FG-disproof brief (landed last; its
caveats preserved verbatim in the appendix).*

## Headline findings

1. **Our `EHall` is the classical conjecture, exactly.** `EH θ`
   (`Salt/Maynard.lean:113`) is the textbook form — all moduli `q ≤ x^θ`, max
   over reduced residues, absolute values, π-normalization, `(log x)^A` saving
   for every `A`; `EHall` (`Salt/Twelve/Params.lean:33`) is `∀ θ ∈ (0,1)`. The
   literature's verdict on that exact shape: **provably false at the top**
   (every log-power level `x/(log x)^B` — Friedlander–Granville 1989; the
   1968 original, a variance statement at log-power level, is thereby dead
   and the modern `∀θ<1` form is a retro-attribution, see I.2),
   **unconditionally true below 1/2** (Bombieri–Vinogradov 1965), and **open
   at every θ ∈ [1/2, 1)** — with no unconditional progress on the classical
   form past 1/2 in sixty years, and provably-identified structural barriers
   (large-sieve duality) rather than mere lack of effort.
2. **Every beyond-1/2 theorem trades away part of our statement shape.** Zhang,
   Polymath8a, BFI, Maynard I–III, Lichtman, Stadlmann, Pascadi (current record:
   level 5/8, 2025) — each needs smooth/well-factorable moduli, a fixed residue
   class, or one-sided weights. None sums the max over residues; the dispersion
   method structurally cannot. GRH does not help: it also stops at 1/2.
3. **The one genuine conditional route to full EH is new and little-known:
   GRH + pair correlation for Dirichlet L-zeros ⇒ corrected-Montgomery ⇒ EHall**
   (Kandhil–Languasco–Moree, Math. Ann. 2026). The price: the pair-correlation
   hypothesis is as unattackable as RH itself. Otherwise EH-beyond-1/2 follows
   from no standard conjecture — it stands alone.
4. **RH is not the gate for any of this.** RH/GRH would make everything
   *effective* (kill Siegel zeros, discharge our `SiegelWalfisz` with a
   computable `K`) but adds no level of distribution beyond 1/2 and cannot
   cross the parity floor. The corpus's honest analytic frontier — the SW gate —
   is "RH-lite": a zero-free-region statement whose full-RH strengthening would
   change constants, not structure.
5. **Siegel zeros are where the three pillars meet.** The `∃K` ineffectivity of
   our frozen `SiegelWalfisz` gate flows, by design, from exactly one point in
   the classical proof: Siegel's 1935 dichotomy on a hypothetical exceptional
   character (verified this session against the line-by-line exposition of
   Goldfeld's 1974 proof — the route our S4 card freezes). Existence of Siegel
   zeros would *prove* twin primes (Heath-Brown 1983; Tao–Teräväinen 2021 get
   the full Hardy–Littlewood asymptotic for pairs); non-existence would make
   our gate effective. Neither side is remotely in reach; Zhang's 2022
   (log q)^{-2022} preprint remains unpublished and unverified as of 2026-07.
6. **Formalizability splits cleanly into three tiers.** BV-at-1/2 = our
   SW-gated chain (`hasLevel_half_of_siegelWalfisz : HasLevel (1/2)` — done
   modulo the gate; nothing foundational blocks the gate itself). EH-beyond-1/2
   needs the Kloosterman stack: mathlib 2026 has Gauss sums but no Kloosterman
   sums, no Hasse bound, no Weil conjectures — decade-scale via the Deligne
   route, hard-multi-year via the Deligne-free curve route. Full EH/RH:
   no formalization question arises; nobody has a proof to formalize. `EHall`
   is a conditional-forever luxury hypothesis — and `no_twin_weight` shows even
   it stops at 12 for this method.

---

## Part I — Elliott–Halberstam

### I.1 What our `EHall` says (corpus formulation, verified against source)

- `Salt/Maynard.lean:90` — `maxDiscrepancy x q` = `Finset.sup'` over residues
  `a < q` coprime to `q` of `|π(x;q,a) − π(x)/φ(q)|` (π-form via `primesCount`).
- `Salt/Maynard.lean:113` — `EH θ`: for every `A > 0` there is `C` with
  `∑_{q=1}^{⌊x^θ⌋} maxDiscrepancy x q ≤ C·x/(log x)^A` for all `x ≥ 2`.
- `Salt/Twelve/Params.lean:33` — `EHall : ∀ θ, 0 < θ → θ < 1 → EH θ`.
- Consumers: `gaps_le_twelve (hPNT : WindowPNT) (hEH : EHall)`
  (`Salt/Twelve/GapsUncond.lean:1061`) and the headline corollary
  `gaps_le_twelve_of_piAsymp (hpi : PiAsymp) (hEH : EHall)`
  (`Salt/Twelve/WindowPNTDischarge.lean:130`). Instantiated at a single θ₊ via
  `EHall_hasEH` → `EH_hasLevel`.
- Two in-house precision points. (i) The literature usually states EH in ψ/Λ
  form; π-form and ψ-form are equivalent by partial summation, and our BV chain
  is ψ-form (`psiAP`) bridged by `Salt/BV/PsiToPi.lean`. (ii) `EH θ` puts
  moduli up to `x^θ` exactly; the corpus's BV-shaped carrier `HasLevel θ`
  (`Salt/Maynard/Level.lean:28`) keeps the classical `(log x)^B` deflation
  `q ≤ x^θ/(log x)^B`, and `EH θ → HasLevel θ` is the `B = 0` haircut. So
  `EH (1/2)` (the `BoundedGapsFromEH` antecedent) is marginally *stronger*
  than textbook BV, while `hasLevel_half_of_siegelWalfisz : HasLevel (1/2)`
  (`Salt/BV/AbelCore.lean:753`) is textbook BV, exactly. Never conflate the
  two in writeups.

### I.2 History: the 1968 conjecture and the 1989 disproof at the top

*(Dedicated EH-history brief, folded 2026-07-12; quotes verified against live
sources/locally-extracted PDFs by that scout. Its caveats: appendix, scout A.)*

- **Bibliographic record (verified).** P.D.T.A. Elliott, H. Halberstam,
  "A conjecture in prime number theory," Symposia Mathematica IV (INDAM Rome
  1968/69), Academic Press 1970, 59–72 — confirmed across Granville BAMS 52
  (2015) ref [8], Maynard arXiv:1311.4600 ref [1], KLM arXiv:2411.19762
  ref [3].
- **The original conjecture is NOT the modern one — and it is FALSE.** The
  1970 paper never states it as a clean display. Per Wikipedia's "Original
  conjecture" paragraph (uncited, apparent typo — see guards), it is a
  φ(q)-WEIGHTED VARIANCE (Barban–Davenport–Halberstam-shaped) statement in π
  against `li x`:
  `∑_{q≤X} φ(q) max_{(h,q)=1} (π(x;q,h) − li x/φ(q))² ≪ x²/(log x)^A` with
  `X < x(log x)^{−A−1}` — a **log-power level**, far above any `x^θ`. The
  exact display is secondary-only, but the log-power-level FACT is triply
  corroborated: the FG Annals abstract ("disproves conjectures of Elliott and
  Halberstam, and of Montgomery"), the Savalia UNBC-2022 slides ("EH_Λ(Q) for
  Q = x^α/(log x)^B for any α ≤ 1 … α = 1 disproved by Friedlander-Granville"),
  and KLM ("showed the conjecture to be false when x^{1−ε} is replaced by
  x log^{−B} x, with B > 0 arbitrary").
- **Attribution drift (important for the writeup).** The modern `∀θ<1` form —
  our `EHall` — is a *retro-attribution*. BFI, Acta Math. 156 (1986)
  pp. 205–206, verbatim (ψ-form): "It was conjectured by P. D. T. A. Elliott
  and H. Halberstam [3] that (1.4) may hold with Q = x^{1−ε} but even the
  result with Q = x^{1/2} has not yet been achieved." Granville 2015:
  "Elliott and Halberstam conjectured [8] that one can take Q = x^c for any
  constant c < 1." So the surviving "EH conjecture" of the modern literature
  is the θ<1 weakening, attributed to a paper whose own (inferred) conjecture
  sat at log-power level and is now false.
- **The disproof at the top (abstract verbatim, journal page).** J.
  Friedlander, A. Granville, "Limitations to the equi-distribution of primes
  I," Ann. of Math. (2) 129 (1989) 363–382
  (https://annals.math.princeton.edu/1989/129-2/p04): "for any fixed N > 0,
  there exist arbitrarily large values of a and x such that
  `∑_{q < x/log^N x, (q,a)=1} |ψ(x;q,a) − x/φ(q)| ≫_N x`." Read it closely:
  ψ-form, the SAME residue `a` for every `q` (no max needed), and the summed
  error is `≫ x` — as large as the MAIN TERM, a failure by a full power of
  log, not a near-miss. Citation care (scout's caveat 2.4): in the 1989
  construction the residue `a` GROWS with `x`; the FIXED-`a` strengthening
  ("for any fixed a ≠ 0, uniformity in q ≤ x/log^N x fails") is
  **Limitations III**, Compositio Math. 81 (1992), Numdam — NOT the Annals
  paper. Quantitative shape behind it (Granville's 1995 Cramér-symposium
  article): Maier's matrix method (Maier 1985) produces progressions
  over/under-shooting by a fixed factor `1 ± δ_N`.
- **How close to x can the level get?** `Q = x/(log x)^B` fails for EVERY
  fixed B; every fixed θ < 1 remains open; intermediate ranges (e.g.
  `Q = x·e^{−(log x)^δ}`) are NOT settled by any verified statement. In
  Maynard's phrasing, the modern EH conjecture "is essentially the strongest
  possible result of this type." FG 1989 also disproved Montgomery's original
  pointwise conjecture; the surviving corrected form (FG p. 366, via KLM) is
  `ψ(x;q,a) − x/φ(q) ≪ √(x/q)·x^ε` uniformly for `q < x` — which on
  summation over `q ≤ x^θ` gives exactly `∀θ<1` and no more: the
  corrected-Montgomery and EH frontiers coincide.

### I.3 The unconditional record — and the load-bearing negative

- **Bombieri–Vinogradov 1965** (E. Bombieri, "On the large sieve," Mathematika
  12 (1965) 201–225; A.I. Vinogradov, Izv. Akad. Nauk 1965): for every `A`
  there is `B(A)` with
  `∑_{q ≤ x^{1/2}/(log x)^B} max_y max_a |ψ(y;q,a) − y/φ(q)| ≪_A x/(log x)^A`.
  Level of distribution 1/2, i.e. `EH θ` for every θ < 1/2 — "GRH on average."
- **The load-bearing negative, verified against modern surveys.** For the
  CLASSICAL form — all moduli, max over reduced residues, absolute values —
  **no unconditional result exceeds level 1/2**. Sixty years after BV, the
  record for our exact statement shape is still θ < 1/2. Every entry in the
  I.4 table modifies the statement. Framing sources: Polymath8a's background
  (arXiv:1402.0811 §1), Granville's survey "Primes in intervals of bounded
  length" (Bull. AMS 52 (2015) 171–222), Soundararajan's GPY survey (Bull. AMS
  44 (2007) 1–18).

### I.4 The beyond-1/2 landscape — what each theorem trades away

Predecessor: Fouvry–Iwaniec (1980–83) first broke 1/2 for primes with
fixed-residue/well-factorable restrictions (exact exponents: see precision
guards); Bombieri–Friedlander–Iwaniec then set the classical benchmark.

| Result | Level | Traded away vs. our `EH θ` | Source | Confidence |
|---|---|---|---|---|
| BFI I–III (1986–89) | `x^{4/7−ε}` | **well-factorable weights** (linear-sieve form), **fixed residue** `a`; I: Acta Math. 156, II: Math. Ann. 277, III: J. AMS 2 | via arXiv:2006.07088 intro | primary-verified (level) |
| Zhang 2013 | `1/2 + 1/584` (MPZ(ϖ,δ), **ϖ = δ = 1/1168**) | squarefree `x^δ`-smooth moduli + fixed/CRT residue | Ann. of Math. 179 (2014); parameters via Tao/Sutherland expositions | secondary (parameters) |
| Polymath8a 2014 | `1/2 + 7/300` (MPZ under `600ϖ + 180δ < 7`) | smooth squarefree moduli + CRT residue conditions | arXiv:1402.0811 | primary-verified (7/300) |
| Maynard I 2020 | moduli to `x^{11/21}` | **fixed residue**, moduli with a convenient-sized factor, "all but few" moduli | arXiv:2006.06572 | primary-verified |
| Maynard II 2020 | `x^{3/5−ε}` | **well-factorable weights** (beats BFI's 4/7); `x^{7/12}` for linear-sieve weights | arXiv:2006.07088 | primary-verified |
| Maynard III 2020 | `x^{1/2+δ}` | uniform in residue, moduli with conveniently-sized divisors | arXiv:2006.08250 (Memoirs AMS 306, 2025) | primary-verified (qualitative); δ unverified |
| Lichtman 2022 | `x^{17/32}` | fixed residue (shifted primes; prior 11/21, BFI 29/56) | arXiv:2211.09641 | primary-verified |
| Lichtman 2023 | `66/107` uncond.; `5/8` under Selberg eigenvalue conj. | **triply well-factorable weights** (Goldbach application) | arXiv:2309.08522 | primary-verified |
| Stadlmann 2023 | `1/2 + 1/40` | smooth moduli, on average (improves 8a's 7/300); gives `p_{n+m}−p_n = O(e^{3.8075m})` | arXiv:2309.00425 | primary-verified |
| R. Li 2025 | `10/19` (abstract; a `65/123` version-conflict unresolved) | smooth moduli, **one-sided minorant** only | arXiv:2505.09629 | primary-verified (10/19) |
| **Pascadi 2025 — current record** | **`5/8 − o(1)` unconditional** | **triply well-factorable weights** (Selberg-conjecture dependence removed; Maass-form large sieve/Kuznetsov) | arXiv:2505.00653 | primary-verified |

Reading the table: the "level" column climbs toward 5/8, but **no row has all
three of {all moduli, max over residues, absolute values}** — i.e. no row is a
partial `EHall`. For our Maynard-weight consumers only the classical form (or
GEH) plugs in.

### I.5 The blockers, precisely

1. **Large-sieve sharpness at √x.** The large sieve
   `∑_{q≤Q} ∑*_{a(q)} |∑_{n≤N} a_n e(an/q)|² ≤ (N + Q²)∑|a_n|²` is optimal:
   the ≍ Q² Farey fractions of denominator ≤ Q are `Q^{-2}`-well-spaced, and a
   duality/counting argument shows neither term can be improved (Montgomery,
   "The analytic principle of the large sieve," Bull. AMS 84 (1978);
   Iwaniec–Kowalski ch. 7). BV runs on exactly this inequality, and `Q² ≤ x`
   forces `Q ≤ x^{1/2}`: **level 1/2 is the large sieve's own wall**, not an
   artifact. Beyond it one must replace mean-square counting with genuine
   cancellation in specific bilinear/Kloosterman sums.
2. **The Kloosterman/algebraic-geometry dependency chain.** All beyond-1/2
   results run on the dispersion method (Linnik) + exponential-sum bounds:
   individual Kloosterman sums via **Weil's RH for curves** (1948;
   `|K(a,b;p)| ≤ 2√p`), and the deeper sums-of-products/correlations
   (Birch–Bombieri in BFI III, Zhang's and Polymath8a's Type III estimates)
   via **Deligne's Weil II** (Publ. IHÉS 43 (1974), 52 (1980)). Nuance worth
   preserving: Polymath8a documented a Deligne-free variant — Weil-for-curves
   plus the q-van der Corput method already yields *some* level beyond 1/2,
   with a smaller exponent (arXiv:1402.0811; flagged secondary in the guards).
   So the irreducible dependency for "any beyond-1/2 at all" is RH for curves;
   Deligne buys the strong exponents.
3. **The max-over-residues obstruction.** The dispersion method opens
   `|∑ ...|²` and reorganizes the off-diagonal into Kloosterman-type sums —
   which requires the residue class `a` to be FIXED (or CRT-structured) so the
   square can be expanded against it. Taking `max_a` before summing destroys
   exactly that structure; this is why every dispersion-based row of the I.4
   table carries a fixed-`a` or weight restriction (BFI I intro;
   Friedlander–Iwaniec, *Opera de Cribro*, AMS Colloq. 57, 2010).
4. **GRH does not imply EH beyond 1/2.** GRH gives
   `|ψ(x;q,a) − x/φ(q)| ≪ x^{1/2} log²x` per modulus; summing over `q ≤ x^θ`
   yields `x^{θ+1/2} log²x`, nontrivial only for θ < 1/2. So GRH recovers BV
   (with better uniformity) and **nothing more**: EH at any θ > 1/2 is
   strictly beyond GRH (standard observation; Friedlander–Iwaniec *Opera de
   Cribro*; Granville BAMS 2015 survey).

### I.6 Conditional and heuristic status — does anything imply EH > 1/2?

- **GRH: no** (I.5.4). **GLH: no** — Lindelöf-type hypotheses hit the same
  sum-over-moduli wall; no standard L-function hypothesis is known to give the
  classical form past 1/2 (scout synthesis + survey framing; see guards).
- **The one live implication (recent).** Kandhil–Languasco–Moree, "Pair
  correlation of zeros of Dirichlet L-functions: a possible path towards the
  conjectures of Chowla, Elliott–Halberstam and Montgomery" (arXiv:2411.19762;
  Math. Ann. 394:43, 2026): **GRH + a pair-correlation conjecture for Dirichlet
  L-zeros ⇒ Montgomery's conjecture (corrected form) ⇒ full EH.** The
  elementary bridge: corrected Montgomery
  `|π(x;q,a) − π(x)/φ(q)| ≪_ε (x/q)^{1/2}x^ε` summed over `q ≤ x^θ` gives
  `≪ x^{(1+θ)/2+ε}`, beating `x/(log x)^A` exactly for θ < 1. So EH now sits
  one (unattackable) correlation hypothesis above GRH — a genuine change to
  the folklore "EH follows from nothing."
- **Montgomery's conjecture** (Topics in Multiplicative Number Theory, 1971):
  the original pointwise form `≪_ε x^{1/2+ε}/q^{1/2}` uniformly to `q < x` was
  **disproved** by Friedlander–Granville 1989 in the range `q > x/(log x)^B`;
  the surviving corrected form (FG p. 366, via KLM) is
  `ψ(x;q,a) − x/φ(q) ≪ √(x/q)·x^ε` uniformly for `q < x` — the strong
  pointwise conjecture that implies EHall (I.2). Status: believed in
  corrected form; no approach known.
- **Net honest answer:** EHall is believed on Cramér/heuristic grounds and
  because every trade-away relaxation keeps being proven at ever-higher
  levels; but the classical form beyond 1/2 has no unconditional partial
  result, no GRH route, and exactly one conditional route (via pair
  correlation) — itself beyond any current method.

### I.7 GEH — the generalized conjecture and what it buys

- **Statement shape** (Polymath8b, arXiv:1407.4897 Claim 2.6): the EH estimate
  with `Λ` replaced by Dirichlet convolutions `α ⋆ β` of coefficient sequences
  supported on `[x^ε, x^{1-ε}]`-scaled ranges (divisor-bounded), at level θ.
  `GEH[θ]` for θ < 1/2 is a THEOREM (Motohashi's 1976 convolution/induction
  BV; cited as such by Polymath8b). Beyond 1/2 it is open, like EH.
- **What it buys** (Polymath8b, abstract + §3): `EH[θ<1]` ⇒ gaps ≤ **12**
  (our `gaps_le_twelve` mirrors this, k = 5, H = {7,11,13,17,19});
  `GEH[θ<1]` ⇒ gaps ≤ **6** (k = 3 sieve on convolution data); and **parity
  blocks 6 → 2 for all sieve-type arguments** (Polymath8b §8; the corpus's
  `no_twin_weight` is the k = 2 shard of that wall, kernel-checked).
  Never write "6 under EH" (standing guard, inherited from
  `parity-frontier.md`).
- **Evidential status.** GEH ⊃ EH; the convolution form is exactly as
  plausible heuristically and equally untouchable past 1/2. Its θ < 1/2 base
  case being a theorem (Motohashi) is the reason Polymath8b treated GEH as a
  natural hypothesis rather than a strengthening of faith.

### I.8 Formalizability verdict for THIS corpus

Tiered, against mathlib master as fetched 2026-07-12 (scout F, full audit):

- **Tier 0 — BV at 1/2 (our chain): done modulo the SW gate.**
  `bounded_gaps_of_siegelWalfisz_of_bridge` (`Salt/BV/Headline.lean:26`) +
  `hasLevel_half_of_siegelWalfisz : HasLevel (1/2)`
  (`Salt/BV/AbelCore.lean:753`) is, to our knowledge, the only BV-shaped chain
  in any Lean artifact — mathlib has **no large sieve, no BV** (GitHub +
  docs searches, zero hits). The gate itself (SW) is classical contour-shift
  analysis; the `sw` blueprint's scouts found mathlib readier than folklore
  (Borel–Carathéodory, Jensen, 3-4-1 shape, `LSeries` positivity all present).
  Nothing foundational blocks Tier 0.
- **Tier 1 — EH beyond 1/2: the Kloosterman stack. Decade-scale via Deligne;
  hard-multi-year via the curve route.** mathlib 2026 inventory: Gauss sums
  HAS (`Mathlib/NumberTheory/GaussSum.lean`, algebraic `|g|² = p`);
  **Kloosterman sums: zero hits** — no definition, no Weil bound; Hasse bound
  for elliptic curves: listed in `docs/1000.yaml` with **no decl** (elliptic
  curve group law is formalized, point counting over `F_q` is not); Weil
  conjectures/étale machinery: a 2025–26 *skeleton* exists (abstract sheaf
  cohomology on sites; pro-étale site; a sorry-free `EllAdicCohomology`
  definition proving only trivialities) but none of what Weil II needs —
  no constructible sheaves, no Frobenius action, no trace formula, no weights;
  whole-tree grep for "weil": zero hits. Riemann–Roch for curves: absent.
  PNT itself: sorry-free EXTERNALLY (PNT+ project, Wiener–Ikehara route,
  2024; strong-error-term version by Math Inc's Gauss agent ~Sept 2025,
  claimed sorry-free) but NOT in mathlib proper as of mid-2026; mathlib has
  ζ/Dirichlet-L continuation, functional equation, and non-vanishing on
  `Re s ≥ 1` (Loeffler–Stoll), plus an abstract Selberg sieve — no
  fundamental lemma, no concrete sieve applications, no GPY/Maynard–Tao
  anywhere in Lean. Honest estimate (scout F): BV 1–3 dedicated years;
  Deligne-free beyond-1/2 (Stepanov/Weil-for-curves + dispersion) 3–7 years;
  full BFI/Zhang stack (Weil II) decade-scale at human pace — "comparable to
  building a second mathlib-scale theory."
- **Tier 2 — `EHall` itself: not a formalization target at all.** There is no
  proof to formalize, conditional-forever by every indication above. Its
  honest corpus role: a luxury hypothesis buying **12 vs 600** (k = 5 with
  `EHall` vs the k = 105 CertEval chain on BV alone), stated so the
  conditional theorem is exactly the classical conjecture — and
  `no_twin_weight` (`Salt/TwinBar/Impossibility.lean:276`) proves even `EHall`
  cannot push this method below 12: the k = 2 gate `2·I₂ < J₁+J₂` is
  unsatisfiable (`M₂ ≤ 2 log 2 < 2`, two-sided pin `1.383 ≤ M₂`). The
  hypothesis is honest, load-bearing for sharpness, and permanently
  conditional.

---

## Part II — the Riemann Hypothesis

### II.1 Status ledger (2026)

| Front | Record | Source |
|---|---|---|
| Proportion of zeros on the line | Levinson 1974: ≥ 1/3; Conrey 1989: ≥ 2/5; **Pratt–Robles–Zaharescu–Zeindler 2019/20: > 5/12 ≈ 41.7%** (current) | Levinson Adv. Math. 13; Conrey J. reine angew. Math. 399; PRZZ Res. Math. Sci./arXiv:1802.10521 |
| Numerical verification | all zeros to height **3·10¹²** on the line (Platt–Trudgian 2021); isolated-zero statistics near the 10²⁰-th+ zero (Odlyzko) | Platt–Trudgian Bull. LMS 53 (2021); Odlyzko computations |
| Zero-free region | Vinogradov–Korobov 1958: `σ ≥ 1 − c/((log t)^{2/3}(log log t)^{1/3})` — **exponent 2/3 unimproved since 1958** (constants refined: Ford 2002, Mossinghoff–Trudgian et al.) | standard; Ford Proc. LMS 85 |
| Zero density | **Guth–Maynard 2024**: `N(σ,T) ≪ T^{(30/13)(1−σ)+o(1)}`, first improvement of Ingham 1940's exponent 12/5 near σ = 3/4; primes in short intervals `[x − x^{17/30+ε}, x]` (from 7/12) | arXiv:2405.20552 |
| de Bruijn–Newman | RH ⟺ Λ ≤ 0; **Rodgers–Tao 2020: Λ ≥ 0**; Polymath15 2019: Λ ≤ **0.22**. So RH ⟺ Λ = 0 — "if RH is true, it is only barely true" | Rodgers–Tao Forum Math. Pi 8; Polymath15 Res. Math. Sci. 6 |

### II.2 The strategies (what each actually provides)

1. **Levinson/Conrey mollified moments** — the only engine of unconditional
   partial progress (the proportion ladder above). Asymptotically stuck well
   short of 100%, and 100%-on-the-line would still not be RH (density ≠ all).
2. **Hilbert–Pólya + random matrices** — evidence, not method: Montgomery's
   pair correlation (1973, Proc. Sympos. Pure Math. 24) matches GUE
   (sine-kernel `1 − (sin πu/πu)²`); Odlyzko's computations confirm to
   spectacular accuracy (Math. Comp. 48 (1987) near the 10¹²-th zero; the
   famous 10²⁰-th-zero statistics are the later ~1998–2001 computations);
   Keating–Snaith (Comm. Math. Phys. 214 (2000)) model moments via CUE
   characteristic polynomials. No candidate self-adjoint operator with a
   proof handle has ever been produced.
3. **Berry–Keating** (SIAM Review 41 (1999)): the `H = xp` semiclassical
   picture — a heuristic pointer to what the operator should look like;
   no rigorous quantization exists.
4. **Connes / Weil positivity** (Selecta Math. 5 (1999); Connes–Consani
   2021–25): RH ⟺ positivity of the Weil distribution; recast on the adele
   class space / arithmetic site. An exact reformulation-and-program — the
   positivity remains exactly as unproven in the new language.
5. **The function-field model — the one place the analogue is a THEOREM.**
   Weil 1948 (curves), Deligne 1974/1980 (varieties; Weil I/II): over `F_q`
   there is a geometry (the variety), a cohomology (étale/ℓ-adic), a Frobenius
   whose eigenvalues are the zeros, and a positivity (Castelnuovo/Poincaré
   duality) that pins their absolute value. **The entire proof shape is known;
   what is missing over `Spec ℤ` is the geometry itself.** F₁-geometry,
   Deninger's conjectural cohomology, Connes–Consani — all are attempts to
   build the missing site; none has produced the cohomology.
6. **de Branges** — Hilbert spaces of entire functions; repeated claimed
   proofs; Conrey–Li (IMRN 2000) exhibited counterexamples to the required
   positivity conditions in the relevant cases. Not considered live as stated.

### II.3 The blockers

A. **No operator with a proof handle** (the Hilbert–Pólya gap): nothing to be
   self-adjoint. B. **The missing cohomology for `Spec ℤ`** — the proof shape
   exists (II.2.5) but its habitat doesn't; this is the structural gap, and it
   is the SAME algebraic-geometry stack (étale cohomology, Weil II) whose
   *finite-field half* powers EH-beyond-1/2 (I.5.2). One formalization
   investment, two frontiers. C. **Vinogradov–Korobov stagnation**: the 2/3
   exponent is the exponential-sum technology's own wall — 68 years without
   movement. D. **Λ = 0 means no slack**: Rodgers–Tao's Λ ≥ 0 kills every
   "soft"/perturbative route — any proof must be exactly tight, since the
   claim is a boundary case, not an open condition. E. **Density ≠ all**:
   proportion/density-1 results leave the (possible) exceptional zeros
   untouched, and everything (Siegel, effectivity, error terms) concentrates
   in exactly those.

### II.4 Corpus and mathlib tie-in

- mathlib at this repo's pin (`v4.32.0-rc1`) **has the RH statement**:
  `RiemannHypothesis`
  (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:184` — "constructing a term
  of this type is worth a million dollars"). It has **no GRH statement** for
  Dirichlet L-functions (grep: zero hits) — a GRH-conditional corpus theorem
  would have to state its own `GRH` Prop, exactly as we state `EH`/`EHall`.
- What RH/GRH would buy us: GRH ⇒ `SiegelWalfisz` with an *effective,
  computable* `K` (no Siegel step), ⇒ BV with better uniformity — but still
  only level 1/2 (I.5.4), still gaps ≤ 600-class results, still no twin
  primes (parity, `no_twin_weight`). RH alone (mathlib's statement, ζ only)
  does not even give APs — our chain needs the Dirichlet-L family.
- Our SW arc is "RH-lite": S2–S3 build the quantitative zero-free region
  (3-4-1, Landau–Page), i.e., the unconditional shadow of GRH near `Re s = 1`,
  which is all that PNT-strength AP equidistribution actually needs. Full RH
  would upgrade constants `e^{−c√log x}` → `x^{1/2}` savings; it would not
  change a single statement shape in the corpus.

---

## Part III — Siegel zeros

### III.1 What they are, and the Landau–Page structure

- **Definition** (Montgomery–Vaughan Thm 11.3 via scout I; Elkies, Harvard
  Math 259 notes): in `σ > 1 − c/log(q(|t|+2))`, `L(s,χ)` for χ mod q has no
  zeros — except that a REAL (quadratic) χ may have at most ONE, necessarily
  real and simple: the exceptional/Siegel zero β. "Siegel zero" is
  threshold-relative (a zero is exceptional relative to the constant c chosen)
  — Elkies flags this explicitly.
- **Landau–Page across a range** (Bhowmik–Halupczok arXiv:2010.01308, Thm 1,
  verbatim-verified): for `Q, T ≥ 2` the product `∏_{q≤Q}∏*_{χ(q)} L(s,χ)`
  has **at most one** zero in `|t| ≤ T`, `1 − σ ≤ c/log(QT)`; if it exists it
  is real, simple, attached to a unique quadratic χ. One exceptional character
  per range — the S3 card's "≤1 exceptional zero; one exceptional modulus per
  range" is exactly this.
- **The repulsion behind it** (Landau 1918, Göttinger Nachr. 285–295): two
  distinct real primitive χ₁, χ₂ cannot both have zeros `> 1 − c/log(q₁q₂)`
  (positivity of `ζ·L(χ₁)·L(χ₂)·L(χ₁χ₂)`). Consequence (MV Cor. 11.9):
  exceptional moduli grow as `q_{i+1} > q_i^A` for ANY fixed A (at threshold
  `c(A)/log q_i`) — the folklore "`q_{j+1} > q_j²`" is just A = 2.

### III.2 The bounds ladder (how far can β be pushed from 1)

| Rung | Bound | Effective? | Source |
|---|---|---|---|
| Classical (Page-era) | `1 − β ≫ q^{-1/2} (log q)^{-2}` — from `L(1,χ) ≫ q^{-1/2}` (class number ≥ 1) | **yes** | Elkies M259 notes (chain verbatim-verified) |
| GGZ (the only effective breakthrough) | `L(1,χ_d) ≫ (log|d|)^{1-ε}/√|d|` — i.e. `h(d) ≫ (log|d|)^{1-ε}`; explicit: Oesterlé's `h(d) > (1/55)(log|d|)∏_{p|d}(1−⌊2√p⌋/(p+1))` for `(d,5077)=1` | **yes** | Goldfeld Ann. SNS Pisa 3 (1976) + Gross–Zagier Invent. Math. 84 (1986); Oesterlé Enseign. Math. 34 (1988); Goldfeld's Columbia survey (verbatim-verified) |
| Siegel 1935 | `1 − β ≫_ε q^{-ε}` (⇔ `L(1,χ) ≫_ε q^{-ε}`, ⇒ `h(d) ≫_ε |d|^{1/2-ε}`) | **NO — ineffective for every ε < 1/2** | Siegel Acta Arith. 1 (1935) 83–86; Elkies (verbatim: "remain ineffective almost seventy years later") |
| Tatuzawa 1951 | Siegel's bound, effective **with at most one exceptional χ** | yes-but-one | via Bhowmik–Halupczok §2 |
| Zhang 2022 (preprint) | claims `L(1,χ) > c(log q)^{-2022}`, zero-free `σ > 1 − c(log q)^{-2024}` | claimed effective | arXiv:2211.02515 — see III.4 status |

- **The ineffectivity mechanism, exactly** (this is where our gate's `∃K`
  comes from). Siegel-type proofs split on a hypothetical: **Case 1** — no
  real χ has a real zero in `(1−ε′, 1)`: every constant effective. **Case 2**
  — some (χ₁, β₁) exists: use it to repel all other characters; the constants
  now depend on the *unexhibited* χ₁, β₁. No one can decide which case holds,
  so the final `C(ε)` is well-defined but uncomputable. The "one hypothetical
  bad character repels the rest" trick is the same Landau 1918 positivity
  as III.1.
- **Deuring–Heilbronn repulsion** (Linnik 1944 — the phenomenon carries his
  paper's title; quantitative form Bhowmik–Halupczok Thm 3): an exceptional β
  widens everyone else's zero-free region by the factor
  `log(1/((1−β)log qT))` — the closer β sits to 1, the more it represses all
  other zeros. One of the three principles of Linnik's theorem; current
  explicit constants: Benli–Goel–Twiss–Zaman arXiv:2410.06082 (2024).
- **The GGZ "higher-rank blocker."** Goldfeld's general theorem converts an
  L-function with a central zero of order g into `h(d) ≫ (log|d|)^{g-3}`;
  Gross–Zagier supplied the triple central zero (the rank-3 curve of
  conductor 5077, Buhler–Gross–Zagier 1985), hence one power of log. A power
  `|d|^δ` needs central zeros of unbounded order — no construction is known
  or expected. Stuck since 1985.

### III.3 If they exist: the consequences literature (the parity back door)

- **The mechanism** (Tao–Teräväinen, arXiv:2109.06291, §1.2, verbatim-quoted
  by scout J): a Siegel zero forces `χ(p) = −1` for most primes p at
  conductor scale — μ and Λ "pretend" to be χ and `χ⋆log`. The sieve's parity
  blindness is exactly ignorance of μ's sign; the exceptional character
  supplies it, and prime-counting reduces to divisor-correlations `τ(n)τ(n+h)`
  — solvable because τ has level of distribution 2/3 > 1/2 **via Weil's
  Kloosterman bound** (the same algebraic-geometry input as I.5.2, resurfacing
  on the hypothesis side).
- **Heath-Brown 1983** (Proc. LMS 47, 193–224; precise form via TT Thm 1.5(i)):
  Siegel zeros of quality `η → ∞` (β = 1 − 1/(η log q)) give the twin-prime
  **asymptotic with the Hardy–Littlewood constant** for `x ∈ [q^250, q^300]`,
  error `O(1/log log η)`. Popular dichotomy: *either* no Siegel zeros, *or*
  infinitely many twin primes. This is `parity-frontier.md`'s unique honest
  gate; its verdict — document, don't attempt — stands.
- **Tao–Teräväinen 2021/22** (J. LMS 106): Hardy–Littlewood for pairs
  (k ≤ 2 ONLY) + arbitrary Liouville factors, in the much wider window
  `q^{41/2+ε} ≤ x ≤ q^{η^{1/2}}`, error `O(log^{-1/20} η)`; also Chowla and a
  conditional Sarnak statement. Successors: Matomäki–Merikoski
  (arXiv:2112.11412; IMRN 2023 — uniform `h = O(X)`, so Goldbach-type too),
  Wright (arXiv:2111.14054 — m-tuples of diameter `~e^{1.9828m}`, beating
  EH-conditional bounds; arXiv:2507.10780 — AP level `x^{2/3-ε}` under
  exceptional characters, past anything GRH gives).
- **Friedlander–Iwaniec exceptional-character series**: IMRN 2003 (AP
  asymptotics at level `x^{233/462}`, beyond the GRH barrier — under an
  extreme exceptionality hypothesis, threshold exponent r = 554,401); "The
  illusory sieve" (IJNT 2005: asymptotics for primes `a² + b⁶` — what no sieve
  can do, parity broken); QJM 2013. The genre's lesson: Siegel zeros are a
  *stronger-than-GRH* hallucination — an inconsistency engine believed to
  prove false-in-reality statements en route to a contradiction nobody can
  close.
- **Corpus reading of Heath-Brown** (unchanged from `parity-frontier.md`):
  kernel-checked it would say "twin primes, OR no Siegel zeros — at least
  one," and it needs the exceptional-character L-function stack the corpus
  entirely lacks.

### III.4 What would kill them

- **GRH** — trivially (no real zeros off 1/2 at all). Weaker suffices:
  an effective `L(1,χ) ≫ (log q)^{-1}` (Zhang's target shape), or even
  Sarnak–Zaharescu's Hypothesis H (GRH for *non-real* zeros only) already
  forces strong repulsion (via Basak–Thorner–Zaharescu, Algebra & Number
  Theory 20 (2026), who weaken H to a disk hypothesis H_δ with effective
  thresholds).
- **Granville–Stark 2000** (Invent. Math. 139, verbatim-verified from the
  authors' PDF): the **uniform abc conjecture for number fields** ⇒ no Siegel
  zeros for `χ_{-d}` with **negative discriminant only** — "our proof provides
  no insight into … positive discriminants" (no modular-function theory
  there). Half the problem, conditionally.
- **Iwaniec–Sarnak 2000** (Israel J. Math. 120): if strictly **more than 50%**
  of even holomorphic newforms of level N have `L(1/2, f) ≥ (log N)^{-2}`,
  then no Siegel zeros. Unconditionally they reach **exactly 50%** — the
  program sits at the threshold, a barrier at 50% "intimately connected" to
  the problem itself.
- **Zhang's 2022 preprint** (arXiv:2211.02515, "Discrete mean estimates and
  the Landau-Siegel zero") — scrupulous status as of 2026-07-12: **v1 only,
  no revision, no journal reference, no erratum, no retraction**; expert
  reports of substantive issues (relayed Nov 2022); community sentiment
  strongly doubtful. Even if fully correct it would NOT close the Heath-Brown
  gate: `(log q)^{-2024}` still permits zeros of quality η up to
  `~(log q)^{2023}`, so the III.3 hypotheses stay live. Treat as
  unestablished.
- **The win-win folklore, framed honestly.** "Either Siegel zeros exist (twin
  primes!) or they don't (effective SW/BV!)" does NOT combine into progress:
  the twin-prime side needs infinitely many zeros of unbounded quality — a
  much stronger input than "not eliminable" — while the effective side needs
  a theorem, not a belief. The excluded middle proves only the disjunction;
  each disjunct is expected to be resolved *against* its useful direction
  (no Siegel zeros, but ineffectively). The corpus takes the only honest
  unconditional lane: prove SW with the ineffective `∃K` and carry the
  ineffectivity forward openly.

### III.5 Corpus tie-ins (all verified against source this session)

- **The frozen gate encodes the ineffectivity BY DESIGN.**
  `Salt/BV/Defs.lean:35`: `SiegelWalfisz : ∀ A C, 0 < A → 0 < C → ∃ K, …` —
  the `∃K` after `∀A ∀C` is exactly Siegel's non-constructive constant; the
  `sw` blueprint records "Siegel is UNAVOIDABLE (∀C forces it)". Any consumer
  extracting a numeric `K` from the future `siegelWalfisz_holds` is
  mis-designed; only `∃`-shaped downstream use is legitimate.
- **S4 = Siegel via Goldfeld, primary-verified.** The S4 card's route
  (4-fold product + positivity) is Goldfeld's 1974 PNAS "A simple proof of
  Siegel's theorem"; read line-by-line this session via Liu's completed
  exposition (arXiv:2201.11145): auxiliary
  `f(s) = ζ(s)L(s,χ₁)L(s,χ₂)L(s,χ₁χ₂)`, coefficients ≥ 0 via the Euler-factor
  identity (the 4-fold positivity lemma the card flags as NEW is Liu's
  Lemma 1 shape); the dichotomy is Liu's Lemma 5, and the ineffectivity
  enters there and only there — verbatim: "the implied constant … is not
  effectively computable because χ₁ and β cannot be determined within
  finitely many steps." In Lean: one `Classical.byCases` on
  `∃ χ₁ β, L(β,χ₁) = 0 ∧ β > 1−ε′` at the top of S4 — axiom-clean
  (`Classical.choice` is already in our permitted set), permanently
  non-constructive. **Formalization warning** (new finding): Goldfeld's
  3-page original states its key integral bound without proof and with a
  constant that must NOT depend on q₂; Liu's Lemma 4 (absolute constants
  X, M) is the load-bearing repair — formalize from Liu's account, not the
  PNAS note.
- **S3 = Landau–Page**: the card's "(≤1 exceptional zero; one exceptional
  modulus per range)" is Bhowmik–Halupczok Thm 1 / MV Cor. 11.8–11.9 (III.1);
  the two-character Landau positivity is the same trick S4 reuses — plan the
  Lean lemma once, use twice.
- **Heath-Brown = the roadmap's honest gate** (`parity-frontier.md` headline
  finding 3): verdict unchanged, now with the precise quantitative shape
  (III.3) on record — hypothesis η → ∞, window `[q^250, q^300]`, needs the
  exceptional-character stack we lack entirely.
- **The parity floor is ours, kernel-checked**: `no_twin_weight`
  (`Salt/TwinBar/Impossibility.lean:276`) + `M₂_squeeze`
  (`1.383 ≤ M₂ ≤ 2 log 2 < 2`) — the k = 2 shard of Polymath8b's 6-floor.
  Even `EHall` (even GEH) leaves twins out of sieve reach; only the Siegel
  back door (III.3) or genuinely new mathematics crosses it.

---

## The verdicts

| Hypothesis | Believed? | Any proof route known? | Lean-formalizable? | Corpus role |
|---|---|---|---|---|
| `HasLevel (1/2)` (BV) | THEOREM (1965) | — | **yes — our SW-gated chain; done modulo gate** | the unconditional workhorse (k = 105 → 600) |
| `SiegelWalfisz` | THEOREM (1930s) | classical contour + Siegel | **yes — the `sw` rung; `∃K` ineffective by design** | THE remaining gate |
| `EH (1/2)` exactly | believed — OPEN, a hair above BV (the `B = 0` haircut) | none (BV techniques cap just below) | no proof exists | `BoundedGapsFromEH` antecedent only; consumers should prefer `HasLevel (1/2)` |
| `EHall` (θ < 1) | believed; false at every log-power level `x/(log x)^B` (FG 1989) | none unconditional; GRH+pair-correlation ⇒ it (KLM 2026) | **no proof exists to formalize** | luxury hypothesis: 12 vs 600; capped at 12 by `no_twin_weight` |
| GEH (θ < 1) | believed (= EH credence) | Motohashi below 1/2; none beyond | same as EHall | would buy 6, not 2 — we don't state it |
| RH | believed; Λ = 0 boundary case | none (programs only) | statement in mathlib; **no proof to formalize** | not load-bearing anywhere in the corpus |
| GRH | believed | none | no statement in mathlib; we'd state our own | would make SW effective; adds NO level beyond 1/2 |
| No Siegel zeros | believed | none effective (GGZ floor: log) | n/a | its failure mode is priced into the gate's `∃K` |
| Siegel zeros EXIST | believed FALSE | n/a | Heath-Brown chain: research-scale, don't attempt | the parity back door; document-only |

The through-line the title promises: **each pillar stays a hypothesis for an
identified structural reason** — EH beyond 1/2 sits behind the large sieve's
own sharpness and the dispersion method's fixed-residue trade; RH sits behind
a missing geometry whose finite-field shadow is, not coincidentally, the same
Weil/Deligne stack EH-beyond-1/2 runs on; and effectivity sits behind Siegel's
dichotomy on a character nobody can exhibit. The corpus prices all three
honestly: `HasLevel (1/2)` proven-modulo-SW, `EHall` conditional-forever and
capped at 12 by our own impossibility theorem, ineffectivity carried as `∃K`.

## Precision guards (flag before quoting)

1. **Scout-log dependency.** Sections I.5, I.6 (GLH/pair-correlation
   framing), II.1–II.3 rest on scout briefs whose verbatim quotes live in the
   session log, not re-checked against the printed sources by me line-by-line
   (exceptions — personally primary-verified this session: the KLM abstract,
   the original-EH and FG-1989 statement shapes (Savalia–Vatwani slides read
   as rendered pages), Liu's Goldfeld exposition pp. 1–5,
   Granville–Stark's scope quote, TT's Thm 1.5/1.6 shapes, the whole of
   III via scouts I/J who quoted verbatim from fetched PDFs, mathlib source
   at our pin, and every corpus lemma cited).
2. **Original-EH display (I.2).** The exact original variance display rests
   SOLELY on Wikipedia's uncited "Original conjecture" paragraph (which
   contains an apparent typo, `∑_{q≤x}` vs. the `X` side-condition); the 1970
   Symposia text itself is not openly digitized and was NOT fetched by anyone
   this session. The log-power-LEVEL fact is what is triply corroborated
   (FG abstract, Savalia slides, KLM); the FG-1989 abstract is verbatim from
   the Annals journal page; the BFI-1986 retro-attribution quote is verbatim
   from the Acta paper. Anyone quoting "Elliott and Halberstam wrote…" must
   pull the original first. Keep Limitations I (Annals 1989, growing `a`)
   vs. Limitations III (Compositio 1992, fixed `a`) straight.
3. **Zhang's ϖ = δ = 1/1168** and the MPZ bookkeeping: via Tao/Sutherland
   expositions, not the Annals text. Polymath8a's `600ϖ + 180δ < 7`:
   secondary; the 7/300 headline is primary-verified.
4. **Fouvry–Iwaniec exact exponents** (early 80s): secondary-only; the memo
   deliberately states no number for them. Do NOT quote "1/2 + 1/230" as a
   primes level — that figure is the ternary-divisor exponent
   (Friedlander–Iwaniec 1985).
5. **Motohashi = GEH below 1/2**: stated on Polymath8b's citation, not from
   Motohashi's 1976 paper directly.
6. **BFI per-paper statement split** (which of I/II/III carries which
   restriction): the 4/7 level and the well-factorable/fixed-a trades are
   solid; the per-paper attribution of each variant was not pinned to page
   numbers.
7. **Montgomery–Vaughan and Iwaniec–Kowalski numbering** (Thm 11.3,
   Cor 11.8/11.9, ch. 7/11): via a careful secondary transcription (UBC
   note); verify against the books before quoting numbering.
8. **Iwaniec–Sarnak threshold fine print** (the `(log N)^{-2}` smallness
   condition and family scope): via a restatement in arXiv:1605.02434, not
   the Israel J. Math. original.
9. **StrongPNT (Math Inc, Sept 2025) sorry-free status**: claimed by the
   project, not independently audited; PNT+ itself checked directly.
10. **Polymath8a's Deligne-free variant scope** (I.5.2): stated from the
    paper's known structure; exact weaker exponent not re-verified this
    session.
11. **"No standard conjecture implies EH > 1/2 except KLM"** (I.6): the
    negative half is a synthesis (no survey states it as a theorem-shaped
    absence); the KLM half is primary-verified. Frame the negative as
    "we know of none," not "there is none."
12. **Zhang 2022 status**: checked directly on arXiv (v1 only) 2026-07-12;
    the "substantive issues" report is blog-relayed expert comment
    (K. Conrad via Woit, Nov 2022) — attribute as such, never as a published
    refutation.

## Appendix — scout COULD-NOT-VERIFY sections, preserved verbatim

Scouts A (EH history/FG), I (Siegel structure), J (Siegel consequences), and
F (mathlib) returned explicit caveat lists; they are preserved here verbatim
(light re-wrapping only). Scouts B/C/D/E/G/H's caveats were folded into the
guards above and the table's confidence column; their full text lives in the
session transcript.

### Scout A (EH history and the Friedlander–Granville disproof)

1. The original Symposia Mathematica text itself (not digitized openly); the
   exact original display rests solely on Wikipedia's uncited paragraph (with
   typo).
2. FG 1989 full text (JSTOR paywall) — only the journal-page abstract
   verified; internal theorem numbering and the p. 366 Montgomery wording
   rest on KLM.
3. Montgomery 1971 original wording — not fetched.
4. Intermediate ranges (between all `x^θ`, θ < 1, and `x/(log x)^B`) —
   unaddressed.
5. Opera de Cribro — inaccessible.
6. Grokipedia — 403, unused.

### Scout I (Siegel structure/ladder)

1. **Montgomery–Vaughan theorem/page numbers** (Thm 11.3 p. 360, Cor 11.8/11.9
   p. 368, Thm 11.11 p. 370, Thm 11.14/Cor 11.15 pp. 372–373): taken from the
   Bao–Vo UBC student note, which quotes them with page numbers; I could not
   open MV itself. The note is careful but is a secondary transcription.
2. **Iwaniec–Kowalski chapter/theorem numbers**: NOT verified — no fetchable
   copy. Do not cite IK numbering without checking the book. Same for
   **Davenport MNT chapter numbers** (ch. 14 / 20 / 21): Wikipedia cites
   "Davenport (1980) ch. 14 eq. (11)" and Elkies cites "Chapter 20 of
   [Davenport 1967]" for PNT-in-APs error terms, but I could not verify that
   Siegel's theorem is "ch. 21" from a fetched source.
3. **Goldfeld's BAMS 1985 survey** ("Gauss' class number problem for imaginary
   quadratic fields", Bull. AMS 13 (1985), 23–37): bibliographic data verified
   twice (Goldfeld's own reference list, Elkies' reference list), but ams.org
   returned 403 — content not read. Everything attributed to "Goldfeld's
   survey" comes from his later Columbia exposition (GaussProblem.pdf), read
   in full.
4. **Stopple's Notices article** (2006): ams.org 403; the
   Hecke/Deuring/Mordell/Heilbronn dichotomy history rests on search-result
   snippets (encyclopedia.com Heilbronn biography) plus standard accounts.
   The specific claims "Hecke's theorem appears in Landau's 1918 paper",
   "Deuring 1933: RH false ⟹ h ≥ 2 eventually" (Math. Z. 37, 405–415),
   "Mordell 1934" are consistent across secondary sources but no primary
   statement was fetched.
5. **The "higher rank blocker" prose:** the mechanism (exponent g−3 in
   Goldfeld's general theorem ⟹ power of |D| needs unbounded central
   vanishing order) is verified from Goldfeld's survey, but no verbatim
   primary-source sentence says "improving log|D| to |D|^δ requires zeros of
   arbitrarily high order". Treat the formulation as an accurate paraphrase,
   not a quote.
6. **Landau 1936 intermediate bound** β < 1 − C(ε)|D|^{−3/8−ε} and its claimed
   ineffectivity: Wikipedia "Siegel zero" only. The safe citation for
   Siegel's paper is Acta Arith. 1 (1935), 83–86 (confirmed in Elkies'
   references; some sources date it 1936).
7. **Oesterlé's constant:** 1/55 with the ∏(1 − ⌊2√p⌋/(p+1)) correction and
   the (D,5077)=1 condition is verified verbatim from Goldfeld's survey; the
   "1/7000" version appearing in MathWorld/Grokipedia search results was not
   traced to a primary source. Prefer 1/55.
8. **Tao's Landau–Page location:** his Notes 7 cites "the Landau-Page theorem
   (Exercise 54 from Notes 2)" — the exercise text itself was not extracted.
   The Bhowmik–Halupczok Thm 1 and Elkies statements are the reliable
   quotable forms.

### Scout J (Siegel consequences/eliminations)

1. **Heath-Brown 1983 original text**: OUP and Wiley are paywalled (HTTP 402).
   His Theorem 1 and hypothesis shape are taken from Tao–Teräväinen's Theorem
   1.5(i) restatement (primary, peer-reviewed) and the Wikipedia dichotomy.
   The exact wording of HB's own hypothesis in the paper (his constant, his
   exact "infinitely many zeros" formulation) was not seen.
2. **Friedlander–Iwaniec IMRN 2003 in-paper theorem**: full text paywalled;
   exact exponents (r = 554,401, θ < 233/462) taken from Wright's 2025
   restatement (arXiv:2507.10780, Theorem 2.1), read directly. The IMRN
   abstract itself was read directly.
3. **"The illusory sieve" exact theorem**: World Scientific paywalled; the
   a²+b⁶ statement and the (log D)^{−200} normalization come from Merikoski's
   arXiv intro (read directly) plus the journal abstract.
4. **"Exceptional discriminants are the sum of a square and a prime" (QJM 64,
   2013)**: bibliographic data and statement from search records/ResearchGate
   only; theorem not read.
5. **Iwaniec–Sarnak (log N)^{−2} threshold**: the abstract (verbatim) and the
   BPZ characterization are solid; the specific "c > 1/4 of all newforms with
   L(1/2,f) ≥ (log N)^{−2}" formulation rests on the restatement in
   arXiv:1605.02434 — the Israel J. Math. paper itself was not read. The IS
   conditional statement's precise conclusion scope (which conductors get
   eliminated, uniformity in N vs D) was not pinned down from the original.
6. **Sarnak–Zaharescu**: description taken from Basak–Thorner–Zaharescu's
   citation [8]; bibliographic details not independently confirmed (commonly
   cited as Duke Math. J. 111 (2002), 575–587 — verify before quoting).
7. **Chinis JLMS 2026 published version**: Wiley paywalled; statement from the
   arXiv abstract + Wiley listing metadata.
8. **Zhang status**: there is no citable formal referee outcome, erratum, or
   retraction in either direction; the "substantive issues" report is a
   blog-relayed expert comment (K. Conrad via Woit, Nov 14 2022), and the 5%
   figure is a prediction market. Absence of v2/journal-ref on arXiv was
   checked directly (2026-07-12).
9. **Wikipedia's "Granville 2020" parity-optimality claim** (under Siegel
   zeros the parity-limited sieve upper bounds are optimal): underlying paper
   not located/checked.
10. **Drappeau–Maynard** (Kloosterman sums along primes under exceptional
    characters, PAMS 147 (2019)): attribution and venue from Merikoski's
    intro and an AMS search hit; paper not read.

### Scout F (mathlib distance)

- **StrongPNT sorry-free/axiom-clean status:** claimed by Math Inc; not
  independently confirmed from the repo (no sorry-count or `#print axioms`
  audit found). Completion date "Sept 2025" is from an X post by Jesse Han
  and press (nowadais 2025-09-14), not a repo-tagged release.
- **Whether PNT+'s Wiener–Ikehara PNT has a merge-into-mathlib PR in flight**
  — evidence of absence (100.html, zeta docs) is current, but no explicit
  "pending/rejected" statement was found.
- **Archimedean `|gaussSum| = √p` lemma:** not found in the three Gauss-sum
  files; a full-text sweep of all of mathlib for a norm-valued version was
  cut short by GitHub search rate limits.
- **Polymath8a's "Deligne-free" variant** (a level of distribution beyond 1/2
  using only one-dimensional/curve exponential sums, at the cost of a weaker
  bound): stated from mathematical background knowledge (the Polymath8a
  paper, arXiv:1402.0811, discusses avoiding Deligne's theorems); the exact
  scope of that variant was NOT re-fetched and verified this session. Treat
  "curve-level route suffices for *some* θ > 1/2" as secondary-only.
- **Chebyshev/Mertens estimates in mathlib:** marked PARTIAL by inference
  (prime-counting function exists, PNT-strength asymptotics don't); exact
  lemma inventory not enumerated.
- **Authorship/attribution of the mathlib Selberg sieve** (Zulip thread
  suggests a single contributor drove it): doc page verified directly,
  contributor identity not pinned down.
- **Per-declaration introduction dates:** docs pages carry no timestamps; all
  "HAS" claims reflect `master` as fetched 2026-07-12, with file-level
  last-commit dates (2026-03-12 … 2026-07-02) for the newest
  algebraic-geometry modules.
- One background subagent (sieve cluster) had not reported by deadline; its
  items (large sieve, Selberg sieve, BV, bounded gaps) were independently
  verified by direct searches, so no coverage gap remains — but those four
  verdicts rest on a single direct pass rather than two independent passes.
