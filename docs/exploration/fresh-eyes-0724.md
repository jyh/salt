# FRESH-EYES consult brief — papers/flagship/main.tex (2026-07-24, Friday eve)

*The ratified fresh-eyes pass (council item 1, run Friday eve per the granted
flexibility). Reviewer: a cold Opus 5 agent with ZERO session context — by
design the freshest read available before Sunday's the approval review. Read the
full 782 lines cold, then verified a dozen claimed declarations against the
Lean source (all names exist — no fabrication). READ-ONLY: no edits made;
every edit below is JYH-gated (paper edits only through ratified rounds).
Maestro spot-verified the three sharpest factual claims before banking:
255-vs-252 real (L70/L119 vs L664); the lean4checker sentence at L153;
TaoChowla in the bibliography, never cited in text.*

## 1. The three sentences a hostile referee quotes back

**(a) L49–51 (abstract).** "We introduce the fulcrum: the weakest hypothesis
yet formulated under which Siegel zeros produce infinitely many twin primes."
The paper never proves the fulcrum produces twin primes — that is exactly
`h_Engine`, which L350–354 concedes is unproven. The abstract's headline
asserts the one implication the paper disclaims. "Weakest yet formulated" is
an uncited comparative against all literature; L300–301 claims minimality
only relative to *this* engine.

**(b) L152–155.** "before submission the build is run through an independent
checker (`lean4checker`); two unrelated implementations agreeing shrinks the
kernel-bug hypothesis below the noise floor of any classical refereeing
process." **Factually wrong and trivially checkable by exactly its audience**:
the shakedown record (pilot.md ~:10909) shows standalone lean4checker is
deprecated into Lean's built-in `leanchecker` — the SAME kernel
implementation, not an unrelated one; 259 salt-authored declarations
re-checked in default mode with one `--fresh` replay (Keller, not the NT
tracks). The sentence sits at the load-bearing point of the trust argument.

**(c) L675–677.** "at no point in the campaign did the kernel discover an
error. It confirmed; the adversarial layers discovered." Read literally: no
proof attempt ever failed to compile — which no reader believes. Adjacent:
"255 catches against zero wrong proofs" (L119, L70) — a wrong proof is by
construction impossible past the kernel, so the denominator is a tautology,
not evidence. The single easiest shot at the method claim.

## 2. The first-ten-minutes read — promised vs delivered

After abstract + intro a smart reader believes: Siegel zeros now yield twin
primes under a weakest-known hypothesis; a "twins or no Siegel zeros"
dichotomy is proven; log-Chowla is nearly cracked; the parity barrier is now
a theorem. Delivered:

- **The dichotomy is three lines of `by_cases`**
  (`Salt/Fulcrum/Dichotomy.lean:102–107` — LEM +
  `not_fulcrum_implies_noSiegelZeros`, `hEngine` assumed). Honest at
  L350–354, but Theorem 5.1 is presented as the headline; a referee will call
  the statement vacuous decoration on an assumption.
- **"the logarithmic two-point Chowla conjecture is reduced" (L67–68).** Tao
  PROVED the two-point logarithmic Chowla statement in 2016 — `\cite{TaoChowla}`
  is in the bibliography, never cited in the text. Nowhere does the paper say
  "this is a known theorem; the contribution is its first formalization."
  **Worst single approval hazard in the paper.**
- **The MRT door.** "reduced to a single named hypothesis" understates that
  the door IS the MR/MRT machinery (Prop 2.4); correctly hedged only at
  L617–624, after the abstract has landed.
- **Chen's theorem (L236–243)** — a fully machine-checked Chen is a landmark
  appearing in a subordinate clause as "inherited infrastructure" with the
  hedging indefinite article. Simultaneously the biggest underclaim and an
  overclaim risk (no statement given). Also L243 says these "are indexed in
  Appendix A" — **they are not** (12 headline rows only).

## 3. Load-bearing vagueness (each a referee stop)

- **Theorem 3.4 has no statement** (L230–234). And
  `Salt/Vmvt/MeanValue.lean:169–173`: `VmvtBound` is the CLASSICAL Vinogradov
  estimate (`E(k,r) = 2rk − ½k(k+1) + η(k,r)`, η > 0), not the sharp main
  conjecture (BDG/Wooley 2016). Calling it "the Vinogradov mean value
  theorem" unqualified, formula unprinted, is the most attackable line in §3.
- **The central constant is undefined**: L275 `C* = max(C^(1), 2/c₀)` —
  `C^(1)` never defined. Likewise `‖1−ρ‖` (L270) never defined.
- **Table 1's caption is false** (L704 "Nothing else in the paper is
  conditional"): Theorem 7.1 is conditional in its own statement (L454) and
  its Lean docstring (`Salt/HB/SignRate.lean:50–52`, "hbudget-conditional,
  pending the character master (hb_l2c_masterGen, comment-frozen)"); the Lean
  proof of the conjunct is `exact hbudget`. Theorem 7.1 is not in Table 1.
- **"the engine's regime" (L396) / "its four explicit hypotheses" (L413)
  never stated** (they are `100^16 ≤ z`, `Lwin(x)^8 ≤ z`, `z^3 ≤ x`, `χ²=1`)
  — without them Theorem 6.1 is not self-contained and `e^{5z₀}` looks
  catastrophic.
- **"the certified A₀ range" (L533/L543) never stated** (Lean: `1 ≤ A₀ ≤ 2`).
  And `Salt/Parity/Z.lean:673–674` marks both `1 ≤ A₀` and `E(𝟏)` as UNUSED —
  the "true" leg of Theorem 7.2 is decorative; the theorem is stronger than
  advertised, and a Lean-reading referee sees hypotheses that don't work.
- **Uncited comparisons, all priority-bearing**: L205–207 (strongest
  previously formalized zero-free regions — vs which project?); L344 (Tao's
  formulation; Landau–Page "only one that can occur"); L554–556 (the k=2
  Maynard bound); L485–486 (parity barrier "folklore with heuristics" —
  Selberg's example and Tao's formulation are rigorous and standard).
- **No related-work section; no artifact link.** `Chen1973`, `Littlewood1922`,
  `TaoChowla`, `MR2016`, `MRT`, `Maynard2015`, `HalesKepler`, `companion` all
  in the bibliography, never cited in text. No repository URL/DOI/availability
  statement — while ledger #245–#253 are cited eight times from a private
  repo. A formalization paper with no artifact link gets desk-flagged.
- **L175–177** claims Appendix A "renders every headline statement … side by
  side, reducing the entire correctness question of the corpus to a finite,
  public, refereeable translation audit" — the appendix is a 12-row name
  table marked "[v0.1: headline rows only]". The central trust argument
  points at an appendix that doesn't exist yet; and "the entire correctness
  question" of 324k lines via 12 rows is overreach even when it ships.
- **Hard numeric contradiction: 255 catches (L70, L119) vs 252 (L664).**
- **L66 "census placing the entire corpus inside the parity-invariant cone"**
  vs L548 "Ten headline theorems" — ten instances ≠ 324,724 lines; and
  type-confused (a theorem cannot lie in a cone of weightings; state the
  recast predicate).

## 4. Approval-read hazards (Sunday)

1. "Chowla conjecture reduced" will be heard as "cracked a conjecture" — it
   is Tao's 2016 theorem; say so.
2. **New mathematics vs newly formalized** — the paper never says the plain
   sentence (θ = 3/4 is WEAKER than Vinogradov–Korobov 2/3; a reader cannot
   tell whether the state of the art was beaten or formalized-below).
3. Jargon with no gloss: banners, movements, contract form, the door, the
   spine, the cone, the wall, pretense sum, grade guard, socket.
   "Deuring–Heilbronn repulsion contract" is in the abstract undefined.
4. Lab-notebook voice: L583 "On the day of writing", L622 "landed the same
   day", L668 "five statement-layer faults in one morning", L393 "nine landed
   at first attempt", L410 "What briefly appeared". Reads as changelog; dates
   the paper permanently.
5. AI-collaboration framing: L43–47 "joint work of the author and Claude" —
   the phrase most likely to draw an editorial objection under journal/arXiv
   AI-authorship policies (the `\thanks` and Acknowledgments handle the
   the affiliation question well; authorship is the exposed one).
6. Missing: MSC codes, keywords, affiliation/email, and any statement of what
   a reader should do with the corpus.

## 5. Structural nits (lowest priority)

- §2 (trust) precedes any result; consider after §3.
- No notation block (`‖1−ρ‖`, `L`, `z₀`, `Lwin`); `PS_χ` vs `PS_χ(N)`
  inconsistent (L374 vs L399).
- Em-dash spacing inconsistent (spaced L118/L314/L428/L502 vs unspaced
  L80/L91/L155).
- `\\` inside `\leanname` (L465) will misbehave with the macro definition.
- L185–187 "two had never been formalized at any strength" — name the two.
- `inserts/` (fmin-sweep-comparison.md, windmill-pattern.md) and
  `floor-chen-seed.tex` are NOT referenced by main.tex — confirm intentional.
- No `\label`/`\ref` for §7's degeneracy target; "the grade guard of §7"
  (L169–170) forward-references before §7 exists.

## 6. What genuinely lands — do not weaken

- **§2.1–2.2 (L139–179) minus the lean4checker sentence**: the "mechanically
  excluded vs irreducibly human" split, "Vacuity is an attacked property, not
  an assumed one," the "doubt surface" passage — the best writing in the
  paper; fix the one false sentence and ship the appendix and it is
  referee-proof.
- **The Remark after Definition 4.1 (L291–302)**: "finding a single
  exceptional zero would refute GRH but would not satisfy the fulcrum" —
  precise, self-deflating; best paragraph in the mathematical core.
- **Theorem 7.3 + the reading (L460–479)**: λ as the exact fixed point,
  `PS_λ = 0`, "the character was never load-bearing" — the one result that
  reads as new mathematics; stated crisply, falsifiable as claimed.
- **L123–126** ("conditionality is a first-class citizen … no unconditional
  claim about twin primes") and the **Acknowledgments** — exactly right;
  bring the ABSTRACT into line with L126, not the reverse.

## The ranked lists

**Top five before Sunday:** (1) 255-vs-252; (2) the lean4checker sentence;
(3) Chowla-is-a-theorem-not-a-conjecture; (4) Table 1's caption vs Theorem
7.1; (5) the abstract's fulcrum sentence claiming the unproven engine
implication.

**Before a referee:** related work + artifact link; print Theorem 3.4's
actual statement qualified as the classical η-loss form; define `C^(1)` and
`‖·‖`; print the regimes and the A₀ range; ship Appendix A.
