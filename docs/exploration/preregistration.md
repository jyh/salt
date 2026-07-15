# PRE-REGISTRATION — the salt exploration sprint

**Date: 2026-07-15. Signed by commit** (the hash of the commit
introducing this file is the tamper-evident timestamp; the repository
is private at registration time and this document is disclosed in
full at release, per the ratified protocol in
`docs/writeup/pre-outline.md` §7).

**Declaration.** We pose the six questions below and commit to
reporting ALL outcomes — resolved, refuted, or open-with-precise-
obstruction — together with their costs (tokens, house-session
cycles, human decision points, wall-clock). We do not know the
answers in the sense stated per-question. Questions were frozen
AFTER a reconnaissance pilot (disclosed and excluded: see
`docs/exploration/pilot.md`; its outcomes do not count toward the
pre-registered statistics; its protocol rules R1–R4 and budget
calibration govern the sprint).

**Context at registration.** The corpus contains, kernel-checked and
axiom-clean: Chen's theorem unconditional (`chen_headline`,
2026-07-15), the unconditional Siegel–Walfisz and Bombieri–Vinogradov
chains, the M₂ ≤ 2·log 2 no-go with its enlarged-simplex extension
(δ < δ₀ ≈ 0.4427), and the k=3 sharp-constant core
((3/2)·log 3 < 2, conditional on one 3-D integration lemma). The
method is codified in `docs/METHODS.md` (incl. Part III and the
witness ladder); the sprint is the doctrine's first from-day-one
trial.

---

## The six questions

**Q1 (T1, calibration) — Chen-2.** Formalize: every sufficiently
large even N is p + P₂ (Chen's second theorem). *Known:* the
statement is classically true; our corpus proves the twin form.
*Unknown (the registered quantity):* the REUSE COEFFICIENT — the
marginal cost of the second theorem from the same machinery, in
tokens/nodes/catches, and which renderings prove overfit to the
(n, n+2) shape. *Resolved =* the theorem lands with the cost table;
*informative failure =* a precise inventory of what does not
transfer.

**Q2 (T1½) — the M_k delimitation atlas.** (a) Land TB3-ASM (the 3-D
Fubini assembly) making M₃ < 2 unconditional; (b) extend the
β-tuning pattern (pilot P-C) to k = 4, 5 upper bounds; (c) state and
prove Polymath8b's "pure sieve arguments cannot beat H₁ ≤ 6" as a
formal theorem, or delimit precisely what fragment is provable.
*Known:* the classical values and the β-tuning route. *Unknown:*
whether the assembly and the k ≥ 4 combinatorics stay
executor-tractable, and the exact formal content of (c).

**Q3 (T2) — GEH_min.** Extract the weakest precisely-stated
equidistribution interface that yields bounded gaps ≤ 6 through the
corpus's Maynard machinery (explicit12's variational stack). *Known:*
GEH ⟹ gaps ≤ 6 classically. *Unknown:* the minimal interface — no
such statement exists in the literature; the deliverable is the
interface theorem `GEH_min ⟹ H₁ ≤ 6` with GEH_min visibly weaker
than the folklore statement, or the precise obstruction.

**Q4 (T2) — the windowed-BV variant.** State cleanly, as a standalone
theorem, exactly what our windowed/cutoff Bombieri–Vinogradov chain
proves (the transpose, the guarded per-e rows, the carrier
trichotomy, explicit constants); sweep the literature. *Unknown:*
whether the variant is recorded. *Resolved either way:* unrecorded ⟹
a minor new theorem; recorded ⟹ a confirmed explicit-constants form
with citation.

**Q5 (T3, two legs) — the k = 2 boundary, constrained.**
**(a)** For the marginal-CONSTRAINED enlarged k = 2 functional (the
honest ε-trick class), prove M₂^{[δ]} < 2 for ALL δ ∈ (0, 1] — the
variational form of the parity expectation, unproven at proof level
(our unconstrained bound covers only δ < δ₀ ≈ 0.4427) — or exhibit
precisely where the retuned-CS route fails to use the constraint.
R4 tripwire: a route "reaching 2" implies twins-under-GEH ⟹
definitional alarm, not a result.
**(b)** Within a precisely-defined perturbation class of the (now
landed) Chen razor, either close a P₁-razor from the landed level-½ +
bilinear inputs (R4 alarm: implies twins) or land the obstruction as
a theorem locating where parity bites machinery that transcends the
pure sieve interface. **Placeholder protocol:** the perturbation
class is frozen in a follow-up commit (after a recon+design pass on
the final H-package, per R1/R3) BEFORE any (b) proof work starts;
that commit extends this registration.

**Q6 (T3) — the parity pair.**
**(a) The wall:** the Selberg-witness interface theorem — two
instances of the corpus's `BoundingSieve` interface agreeing in every
field the sieve consumes (1 ± λ weights), one sifted set containing
primes and one none: the parity barrier as a kernel-checked
impossibility theorem about the interface itself. *Known:* Selberg's
construction, classically. *Unknown:* whether it formalizes at our
interface (needs Σλ(n) = o(x)-strength facts; λ is not yet in the
corpus), and the exact class of consumers it delimits.
**(b) The door (stretch):** TwinB_min — the Friedlander–Iwaniec-style
extra axiom for the twin sequence, precisely stated ("here is exactly
what remains, as a theorem"); the implication TwinB_min ⟹ twins
kernel-checked if the timebox allows, precisely stated if not.

*Side task (not a question):* the explicit-constants audit of
intermediates against the published explicit-ANT literature.

---

## Protocol

1. **Timebox:** two weeks from registration, as a STOPPING RULE, not
   a prediction (the pilot ran 40× under its box; the box exists so
   "open, with a precise obstruction" is an honorable outcome).
   Discovery and formal-assembly phases are budgeted separately
   (pilot calibration finding); assembly debts may be scheduled past
   the sprint and reported as such.
2. **Method:** `docs/METHODS.md` in full, including Part III from day
   one — witness-accountability-first (every question opens a
   constraint store), satisfiability witnesses at every freeze,
   adversarial gates before waves, the ceremony per landing. Pilot
   rules R1–R4 (recon precedes freezing, incl. the target's exact
   variational definition; pull-back-onto-landed-theorems first;
   carrier-ambiguity is an early stop; too-good-to-be-true is a
   definitional alarm).
3. **Roles and budget:** designer = the Fable house session; executors
   Opus-tier, explicitly routed; budgets in tokens + cycles +
   decisions; the exploration ledger (`docs/exploration/`) records
   every dispatch, catch, and cost.
4. **Reporting:** the exploration chapter reports all six outcomes
   with the cost table, the catch ledger delta, and the
   cost-vs-distance-from-corpus gradient (the "gold mine" claim,
   measured). Nothing is omitted for being unflattering.

*Ratification trail:* the slate and tiers 2026-07-14 ("yes that's
great"); Q5 two-leg 2026-07-14 ("let's do two legs"); the sprint
start 2026-07-15 ("let's pre-register the sprint so we can get it
started").

---

## Amendments (transparent, post-registration; the frozen text above is
## unedited — the registration hash 7ddeb491665ac2cc82055f0552f467587ee1c494
## certifies the original)

**A1 (2026-07-15, JYH-ratified: "I agree with all three recommendations,
proceed that way").** On Q2bc-recon evidence (the exploration ledger,
2026-07-15 ~11:20):

1. **Q2c reframed** from the registered "H₁ ≤ 6 delimitation statement"
   to **the least-k theorem**: *in the unmodified Maynard–Selberg class,
   the least k with M_k > 2 is 5* (k = 2, 3, 4 closed by the no-go
   atlas; k = 5 achieved by the landed ℚ certificate), with the honest
   gap companion "k = 5 delivers H₁ ≤ 12 at BV-level distribution" and
   the "≤ 6 optimality" recorded as an open note (its sharp half is
   Tao's open problem; the DHL bridge is unlanded). The original
   phrasing conflated three carriers — the recon's R3 early stop is the
   registered-protocol outcome, reported as such.
2. **k=4 assembly scheduling**: N4-ASM-a/b/c run in-sprint only if the
   parity wall (Q6a) closes first; otherwise scheduled past the sprint
   as assembly debt (permitted by Protocol §1).
3. **k=5 upper bound + the Dirichlet real-integral bridge**: recorded
   as debt, not sprint work. The sprint reports the asymmetric honest
   form (ℚ witness > 2 landed; real (5/4)log5 upper bound as debt).
