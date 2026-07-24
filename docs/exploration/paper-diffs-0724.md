# PAPER DIFFS — the ratified editing round (drafted 2026-07-24, Friday eve)

**STATUS: D1–D6 ALL APPROVED BY JYH AND APPLIED verbatim (2026-07-24 evening).**
Count resolved to 256 per the approval. Standing commitment from D2: re-run the
leanchecker replay on the final corpus before arXiv submission. JYH rebuilds
the PDF (no local pdflatex).

*Source: the FRESH-EYES brief (fresh-eyes-0724.md), top five before Sunday +
one bonus. NO edits applied — each diff below is an exact old→new block;
say "apply D1–D6" (or any subset, e.g. "apply D1, D2, D4") and I apply
verbatim and rebuild the PDF is on you / TeX untouched otherwise. Prose is
draft-quality for your edit, per the standing rule. Line numbers refer to
main.tex at commit 0a348c7.*

---

## D1 — the catch count (three sites; the hard contradiction)

The paper says 255 (L70, L119) and 252 (L664). The ledger's highest numbered
entry is **#256** (council-brief-tue21.md:119, "catches through #256",
2026-07-21; halasz-infra-freeze.md's S1-B amendment is #256). Unify all three
to 256. ⚠ CHOICE POINT: if you prefer, re-verify the count at pickup and I
substitute; the diff below uses 256.

**(a) L70, abstract:**
```
OLD: public ledger of every design error caught (255 numbered entries) against
NEW: public ledger of every design error caught (256 numbered entries) against
```

**(b) L119:**
```
OLD: at 255 catches against zero wrong proofs and is offered as evidence that the standard of the first
NEW: at 256 catches against zero wrong proofs and is offered as evidence that the standard of the first
```

**(c) L664:**
```
OLD: The evidence that this discipline works is the ledger: 252 numbered
NEW: The evidence that this discipline works is the ledger: 256 numbered
```

---

## D2 — the lean4checker sentence (L152–155; factually wrong at the trust
## argument's load point)

The facts (our own shakedown record): standalone `lean4checker` is deprecated
into the toolchain's built-in `leanchecker` — the SAME kernel implementation,
not an unrelated one; the shakedown replayed 259 salt-authored declarations
in default mode plus one `--fresh` full replay. The honest claim is
elaborator/cache-fault exclusion, not two-implementations agreement.

```
OLD: and it is checkable: before submission the build is run through an
OLD: independent checker (\texttt{lean4checker}); two unrelated implementations
OLD: agreeing shrinks the kernel-bug hypothesis below the noise floor of any
OLD: classical refereeing process.
NEW: and it is checkable: before submission every declaration is replayed
NEW: through \texttt{leanchecker}, the toolchain's standalone proof checker,
NEW: independently of the elaborator and build cache that produced it. The
NEW: replay does not remove the kernel from the trusted base---checker and
NEW: kernel share an implementation---but it excludes elaborator and cache
NEW: faults, which is where the practical risk lives.
```

⚠ NOTE: this makes "before submission" a commitment — re-run the replay on
the final corpus before arXiv so the sentence is true at submission time.

---

## D3 — Chowla is Tao's theorem (two sites + one citation; the worst
## Sunday hazard)

Tao proved the logarithmic two-point Chowla statement in 2016;
`\cite{TaoChowla}` is in the bibliography and never cited. The contribution
is the machine-checked conditional formalization, and the paper must say so
in the same breath as the claim.

**(a) L67–68, abstract:**
```
OLD: byproduct, the logarithmic two-point Chowla conjecture is reduced to a
OLD: single named hypothesis.
NEW: byproduct, the logarithmic two-point Chowla statement---a theorem of
NEW: Tao---is machine-checked conditionally on a single named uniformity
NEW: hypothesis.
```
(No `\cite` in the abstract per convention; the citation lands in (b).)

**(b) L582–583, §8 opening:**
```
OLD: formalization of the entropy-decrement route to the logarithmic two-point
OLD: Chowla conjecture. On the day of writing, its residual collapsed: the
NEW: formalization of the entropy-decrement route to the logarithmic two-point
NEW: Chowla statement, proved by Tao~\cite{TaoChowla}; the content here is the
NEW: machine-checked reduction, not the truth of the statement. Late in the
NEW: campaign its residual collapsed: the
```
(Also retires one "On the day of writing" lab-notebook timestamp, hazard #4.)

---

## D4 — Table 1's caption vs Theorem 7.1 (the caption is currently false)

Theorem 7.1 (`thm:wall`) is conditional on the overshoot budget (Lean:
`hbudget`, pending the comment-frozen character master `hb_l2c_masterGen`)
and is absent from the table. Add the row; the caption then becomes true.

**Insert before `\bottomrule` (after the `thm:spine` row, ~L700):**
```
NEW: Thm~\ref{thm:wall} & the overshoot budget (\texttt{hbudget}) & \S7 \\
```

⚠ CHOICE POINT: the row's middle cell could instead name the deeper residual
(`hb\_l2c\_masterGen`, comment-frozen). I recommend the budget (it is the
hypothesis the theorem statement itself carries); say the word and I put the
master in a footnote instead.

---

## D5 — the abstract's fulcrum sentence (L49–51; asserts the disclaimed
## engine implication + an uncited "weakest yet formulated")

The engine implication is `h_Engine`, conceded unproven at L350–354;
minimality is proved relative to this engine only (L300–301).

```
OLD: We introduce the \emph{fulcrum}: the weakest hypothesis yet formulated
OLD: under which Siegel zeros produce infinitely many twin primes---a single
OLD: fixed quality constant $C^\star$, one zero per unbounded window, with the
NEW: We introduce the \emph{fulcrum}: a single hypothesis---one fixed quality
NEW: constant $C^\star$, one zero per unbounded window---under which, together
NEW: with an explicitly stated engine hypothesis, Siegel zeros produce
NEW: infinitely many twin primes; the fulcrum is proved minimal for the
NEW: engine that consumes it, with the
```
(The grammar joins the original sentence's continuation "...mathematical
object:" — check the splice reads cleanly after applying; I matched the
comma structure.)

---

## D6 (bonus, referee-quote (c)) — the kernel-never-erred sentence
## (L675–677) + the tautological denominator

Read literally, "at no point did the kernel discover an error" claims no
failed compile ever happened. The meaningful claim is stronger and true:
no landed statement was later retracted, and every catch was made ABOVE
the kernel.

```
OLD: We record one measurement with a claim attached: at no point in the
OLD: campaign did the kernel discover an error. It confirmed; the adversarial
OLD: layers discovered.
NEW: We record one measurement with a claim attached: no design error was
NEW: first discovered by the kernel. Proof attempts failed and were repaired
NEW: as routine, but every one of the ledger's catches was made by the
NEW: adversarial layers above the kernel, at the statement level, before a
NEW: wrong proof was built on it---and no landed statement was later
NEW: retracted. The kernel confirmed; the layers discovered.
```

---

## Explicitly NOT in this round (deferred to the referee-tier round)

Related work + artifact link; Theorem 3.4's printed statement (+ the
classical-η-loss qualification); `C^{(1)}` and `‖1−ρ‖` definitions; the
engine regimes and the A₀ range printed; Appendix A's full table; the
lab-notebook timestamps beyond D3(b); MSC/keywords/affiliation; the
"joint work" authorship phrasing (JYH decision, policy-sensitive — flagged,
not drafted).

## The preserve list (do not weaken while applying)

§2.1–2.2 minus the D2 sentence; the Remark after Definition 4.1;
Theorem 7.3 + its reading; L123–126; the Acknowledgments.
