# S3-HB-R3 DESIGN — the ladder verdicts + the R3b freeze

**Status: FROZEN (house, 2026-07-18 ~02:10) — R3b PENDING GATE.**
Provenance: S3-HB3-R0 (the full-climb recon, ledger ~02:00 — the
authoritative annex; its §1/§4 ARE the R3a/R4 deliverables below).

## The ladder verdicts (adopted from the recon, house-ratified)

- **HB-R3a (the dispatcher box upgrade): DEAD-END, documented —
  DO NOT BUILD.** The √log x geometry is the de la Vallée Poussin
  optimum welded at three coupled points (the saving, the
  zero-free width c₀ = 1/126848, the truncation balance); a
  polynomial box degrades the saving to x²·e^{−c₀/θ} ≈ x²·1
  (c₀ five orders too small). Deeper: ψ₁ is parity-blind — the
  non-exceptional zeros contribute a constant fraction of x² at
  polynomial height; no contour statement isolates the exceptional
  zero without an arithmetic parity-break, which is the SIEVE's
  job. The recon's §1 is the negative-result record.
- **HB-R4 (beyond-level-½ error control): THE PREDICTED DEATH
  RUNG.** Heath-Brown needs level x^{1/2+δ}; the corpus's entire
  cancellation stack (char_LS Q²+13N, the bilinear shells, the
  dispersion BV) stops at level ½ exactly, Kloosterman/Weil is
  absent entirely, and the literature confirms HB requires
  nontrivial Kloosterman bounds. This is the SAME wall the corpus
  hits in Chen (TransposedBV), Maynard (GehTail), and the twin
  door — now confirmed as the Heath-Brown death rung. The wall-doc
  is the recon's §4.
- **HB-R3c (the χ-twisted sieve weight): the boundary-entry rung**
  — stratum-0 re-instantiation + the τ-weighted remainder are
  C-tier (~0.6–1.0M to a partial landing); node (a) (the signed
  twisted main term ↔ the L(1,χ) lower bound) is the D-locus and
  the likely death point. QUEUED behind R3b; dispatched only with
  budget to spare, in full knowledge of the expected death (a
  registered success under Amendment 3's acceptance rule).
- **HB-R5 (assembly): gated behind R4 — unreachable this sprint.**

## The R3b freeze — the correlation STATEMENT (SiegelCorrStrong)

The recon's wave-1 recommendation, adopted verbatim: refute the
silence branch by forcing the hypothesis's zero INTO the
dispatcher's box, then re-run the dispatcher's exceptional-case
template directly — no dichotomy, one conclusion.

File: Salt/TwinBar/SiegelCorrStrong.lean (imports
Salt.TwinBar.SiegelCorr + Salt.SW.ShiftVariants + what the case-iii
template needs; NO .All).

```lean
/-- The strong window: the correlation window PLUS the box-entry
    floor s = √log x ≥ 0.27/a (a = the dispatcher's c₄'-grade
    constant — the executor reads the landed value and pins the
    numeric floor accordingly; the recon's arithmetic at
    a ≈ 9.85e−7: s ≥ 2.74e5, x ≥ exp(7.5e10)). -/
def CorrWindowStrong (q : ℕ) (β x : ℝ) : Prop := ...

/-- THE CORRELATION STATEMENT (HB-R3b): under SiegelSequence, for
    every sufficiently small strength there are exceptional data
    such that at EVERY strong-window scale,
      ‖ψ₁(x,χ) + x^{β₁+1}/(β₁(β₁+1))‖ ≤ K₄·x²·e^{−c₄√log x}
    AND the residue ≥ x²/3 — ψ₁ is DEFINITIVELY large negative:
    the primes correlate with χ, no silence branch. -/
theorem siegel_correlation_strong (hSeq : SiegelSequence) : ...
```

Binding notes (recon-verified): the non-emptiness arithmetic
(c ≤ 2.6e−12 grade; the ∀c∃ order preserved; the numeric check
IN the design record: floor exp(7.5e10) ≤ cap exp(1.57e11·(log q)²)
✓); the β₁-into-box lemma (1−β₁ ≤ 0.4055/s² ≤ 3a/(2s) at the
strong floor); the case-iii template re-run
(psi1_contour_shift_exceptional + landau_one_exceptional_at +
E_shape_bound + residue_lower — all landed). Est. 300–450k,
6–10 nodes, ONE executor after the gate.

## Gate charge (S3-HB3B-GATE)

1. Independently REDO the recon's non-emptiness and box-entry
   arithmetic at the LANDED dispatcher constants (read c₄'/a from
   CharDispatch.lean's proof — the recon read a ≈ 9.85e−7;
   verify) — the HB2 self-refutation precedent makes this the
   kill-check.
2. Trace the case-iii template (CharDispatch L435–532): every
   hypothesis it consumes must be derivable in the strong window
   from SiegelSequence's data (the hzfexc zero-freeness, the box
   membership, T = e^{√log x} constraints) — list each with its
   source.
3. Elaboration probes: the strong-window def + the headline
   statement against the landed SiegelCorr/ShiftVariants.
4. Quantifier order (∃c₄K₄ outermost; ∀c-with-a-ceiling — the
   "sufficiently small strength" shape must not invert).
5. R4: the conclusion stays conditional-correlation (NOT twins);
   the docstring carries the R4/R5 gating and the death-map
   pointers.
