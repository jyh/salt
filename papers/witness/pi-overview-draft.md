# Pi submission — Overview draft (350–500 words)
### Drafted 2026-08-05 (Sancho) for JYH's voicing pass. Facts are
### paper-true; every claim below appears in main.tex. ~430 words.

---

This paper proves two theorems about the entropy-decrement route to
the logarithmically averaged two-point Chowla statement, and every
numbered statement in it is machine-checked: each names its Lean 4
declaration over mathlib, and each carries an axiom audit
(propext, Classical.choice, Quot.sound — nothing else).

The first theorem, the toll, is unconditional. The entropy-decrement
argument spends a budget — the per-symbol entropy of the Liouville
window lies between 0 and log 2, one bit — and spends it along a
tower of scales. We price that tower exactly: along the flat tower
H_{j+1} = H_j·⌊2A log H_j⌋, the telescoped decrement equals a
potential difference to within 5%, and any tower long enough to
exhaust the budget must multiply the doubly-logarithmic width by a
factor in [4^{(20/21)A}, (21/20)·4^A] — exponent pinned within
4.8%, constant within 5%, the continuum value 4^A inside. Crossing
the budget is thus a conservation law rather than an optimization:
the price is fixed, and a design chooses only the coordinate in
which to pay it. The original argument's threshold pays the same
invoice on the scale axis as a triple-exponential floor; the flat
road pays in width and replaces it by a single exponential. A
shape-free version shows the constant threshold is extremal to
within the same 5%.

The second theorem, the pearl, is conditional, and its
conditionality is stated at the statement: at every design constant
A above an explicit floor there is a Chowla regime, with window base
pinned at ⌈e^{e^{3.2A}}⌉, at which the logarithmically averaged
two-point correlation does not fail — on a list of hypotheses given
in full: one analytic constant, eight numeric riders, two carried
predicates. Of that list, one rider was found unreachable along the
proof and one predicate false at the regime the theorem itself
produces — the second refuted by the first theorem's own lower
bound — and both were repaired at the level of the statement. A
chain of six corollaries then removes rider after rider; the last
carries five hypotheses, of which three are met by objects the
development exhibits and two are the Siegel obstruction, named.
Making the classical limit available required a quantifier hoist
that the formal statement, and only the formal statement, made
visible.

We suggest the paper is of interest twice over: for the theorems,
and as a case study in what formalization does to analytic number
theory at research scale — statements repaired rather than proofs
patched, conditionality made exact, and errors caught by the
development's own earlier theorems. The mathematics is joint work
of the author and Claude (Anthropic's Fable 5 and Opus models),
carried out under the author's direction and ratification; the
commit ledger records the collaboration line by line.

---

### Placement notes (not part of the overview)
- The six citation placements ruled earlier ride in main.tex, not
  here; the overview cites nothing by number.
- Voice swept: no "honest", no "load-bearing"; em-dashes present —
  JYH decides per instance.
- If the form's field is tighter than 500 words, cut the shape-free
  sentence and the placement of the collaboration sentence can move
  to the cover letter.
