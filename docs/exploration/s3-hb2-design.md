# S3-HB-R2 DESIGN FREEZE — the μ↔χ correlation core (SiegelCorr)

**Status: FROZEN (house, 2026-07-17 ~19:50) — PENDING GATE.**
Provenance: S3-B-R0 (the narrowed Track-B scope: HB-R1 + HB-R2);
HB-R1 landed (SiegelTwin.lean). The core exploits the LANDED
dispatcher `psi1_char_bound` (CharDispatch.lean:324) — the
residue term `−x^{β₁+1}/(β₁(β₁+1))` it EXPOSES in its exceptional
branch is exactly Tao's Lemma-5 correlation ("the primes pretend
μ = χ"), previously used only to KILL the exceptional character
(the SW gate); HB-R2 inverts the orientation.

## The mathematical shape (honesty first)

The dispatcher yields a DISJUNCTION (clean ψ₁-bound OR
zero-data + residue-approximation); its statement does NOT let one
select the exceptional branch from zero-existence alone (that
selection is explicit-formula work = HB-R3+, out of the narrowed
scope). HB-R2 therefore freezes the honest lift: under the
hypothesis, at every strength c, there are character data and an
UNBOUNDED range of scales where EITHER Λ exhibits the full
correlation (ψ₁ ≈ −residue, with the residue PROVABLY ≥ x²/3 —
the quantitative separation) OR ψ₁ is anomalously SMALL — the
correlation-or-silence dichotomy, with both branches
kernel-quantified. The branch-selection obligation is NAMED in
prose (the HB-R3 door), not smuggled.

## Frozen Lean statements — Salt/TwinBar/SiegelCorr.lean
(imports: Salt.TwinBar.SiegelTwin + Salt.SW.CharDispatch; NO .All)

```lean
open Complex DirichletCharacter

/-- The correlation window: scales where the box constraint holds
    and the residue dominates. -/
def CorrWindow (q : ℕ) (x : ℝ) : Prop :=
  Real.exp ((Real.log q + 2) ^ 2 * 16) ≤ x

/-- **The correlation-or-silence dichotomy** (the HB-R2 core).
    Under the Siegel-zero hypothesis: for every strength c there
    are exceptional data (q, χ, β₁) with 1 − c/log q < β₁ < 1 such
    that at EVERY window scale, either ψ₁(x,χ) tracks the Siegel
    residue −x^{β₁+1}/(β₁(β₁+1)) to exponential accuracy, or
    ψ₁(x,χ) is exponentially small — while the residue itself is
    ≥ x²/3.  The primes either impersonate χ or fall silent; no
    third behavior exists. -/
theorem siegel_correlation_dichotomy
    (hSiegel : InfinitelyManySiegelZeros) :
    ∃ c₄ K₄ : ℝ, 0 < c₄ ∧ 0 < K₄ ∧
    ∀ c : ℝ, 0 < c → ∃ (q : ℕ) (_ : NeZero q)
      (χ : DirichletCharacter ℂ q) (β₁ : ℝ),
      1 < q ∧ χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
      LFunction χ (β₁ : ℂ) = 0 ∧
      1 - c / Real.log q < β₁ ∧ β₁ < 1 ∧
      ∀ x : ℝ, CorrWindow q x →
        (x : ℝ) ^ 2 / 3 ≤ ‖(x : ℂ) ^ ((β₁ : ℂ) + 1) /
            ((β₁ : ℂ) * ((β₁ : ℂ) + 1))‖ ∧
        (‖psi1Chi x χ + (x : ℂ) ^ ((β₁ : ℂ) + 1) /
            ((β₁ : ℂ) * ((β₁ : ℂ) + 1))‖
          ≤ K₄ * x ^ 2 * Real.exp (-(c₄ * Real.sqrt (Real.log x)))
        ∨ ‖psi1Chi x χ‖
          ≤ K₄ * x ^ 2 * Real.exp (-(c₄ * Real.sqrt (Real.log x))))
```

(Executor latitude: the exact CorrWindow constant (the 16 and the
+2) may be adjusted to whatever the box arithmetic needs — the
SHAPE x ≥ exp(C·(log q)²) is frozen; likewise x²/3 may weaken to
x²/4 if β₁ ≥ 9/10 forces it. The ∃c₄K₄-outermost order is frozen
(III.4: one destructuring serves all c). If the dispatcher's
exceptional β₁ cannot be IDENTIFIED with the hypothesis's β₁ —
the dispatcher produces its own zero — STOP AND FLAG; the fix
(state the conclusion with the dispatcher's β₁′ carrying the same
window bounds via Page uniqueness, landau_one_exceptional_at) is
a house re-freeze, not executor latitude.)

Required supporting lemma (in-file):
`corrWindow_box : CorrWindow q x → 3 ≤ x ∧
  Real.log (q * (Real.exp (Real.sqrt (Real.log x)) + 4))
    ≤ 2 * Real.sqrt (Real.log x)`
(the box-constraint discharge — pure log/sqrt arithmetic), and
`residue_lower : β₁ ∈ [9/10, 1) → CorrWindow q x →
  x^2/3 ≤ ‖residue‖` (x^{β₁+1} ≥ x^{2−(1−β₁)} with
(1−β₁)·log x controlled... NOTE: 1−β₁ < c/log q and
log x ≥ 16(log q + 2)² give (1−β₁)log x < 16c(log q+2)²/log q —
NOT small for large q! The residue_lower needs the WINDOW CAPPED
ABOVE: revise — see the case table. The honest window is
two-sided: exp(16(log q+2)²) ≤ x ≤ exp(1/(2c·(1−β₁))-grade...
the executor works from: 1−β₁ < c/log q ⟹ choose the upper cap
x ≤ q^{1/(4c)} — then (1−β₁)log x < c/log q · (1/(4c))·log q =
1/4 ⟹ x^{β₁+1} ≥ x²·e^{−1/4} ≥ x²·(3/4) ⟹ residue ≥ x²·(3/4)/2
≥ x²/3. ✓ And the window is NONEMPTY iff
exp(16(log q+2)²) ≤ q^{1/(4c)} ⟺ 16(log q+2)² ≤ log q/(4c) —
TRUE for q large once c is small... but q comes FROM the
hypothesis at strength c and need not be large! THE FIX: invoke
the hypothesis at strength c′ = min c (the smallness making
q big enough)... q is not controlled from below by c′ either.
GATE CHARGE #1: this window-nonemptiness is the design's known
open corner — the gate must adjudicate the resolution: either
(i) derive q ≥ Q₀(c) from badHyp_false-style arithmetic (a zero
within c/log q of 1 forces q large via the landed
siegel-type bounds — check LFunction_apply_one_pos +
LFunction_one_re_le_mvt gives 1 − β₁ ≥ C/√q-grade ineffectively
via siegel_theorem: 1−β₁ ≥ C(ε)/q^ε, so c/log q > C(ε)/q^ε
forces q ≥ Q₀(c, ε) — EFFECTIVE in the needed direction? С(ε)
is ineffective but EXISTS: for each c the set of admissible q is
cofinal — enough for ∃q) or (ii) re-freeze with the two-sided
window as a hypothesis-parameter. The design PRE-ADOPTS (i);
the gate verifies it.)
```lean
def CorrWindow (q : ℕ) (c x : ℝ) : Prop :=   -- REVISED, two-sided
  Real.exp (16 * (Real.log q + 2) ^ 2) ≤ x ∧
  x ≤ (q : ℝ) ^ (1 / (4 * c))
```

## Case space (III.3‴)

Window nonemptiness (the known corner — gate charge #1: the
siegel_theorem route q ≥ Q₀(c)) × the dispatcher's-β₁ vs the
hypothesis's-β₁ identification (Page uniqueness in the box —
landau_one_exceptional_at / page_cross_modulus; if it resists, the
STOP-AND-FLAG above) × the box constraint at the window floor ×
the residue norm arithmetic (β₁(β₁+1) ∈ [9/10·19/10, 2)) × x vs
(x:ℂ) coercions in psi1Chi × T = e^{√log x} exact form.

## III.3″ witness (in-docstring, symbolic)

At c = 1/100, log q = 10⁴ (hypothetical exceptional data):
window = [exp(16·(10⁴+2)²), q^{25}] — log-nonempty check:
16·10⁸ ≤ 25·10⁴? NO — EMPTY. At log q = 10⁴, need
16(log q+2)² ≤ log q/(4c) = 25 log q ⟺ log q ≥ 16(log q+2)²/25 —
false for ALL q. ⟹ THE PRE-ADOPTED WINDOW IS EMPTY ALWAYS at
this floor constant. THE FLOOR CONSTANT IS WRONG: the box needs
only log q ≲ √log x, i.e. x ≥ exp((log q)²)-GRADE is right, and
the cap needs log x ≤ log q/(4c) — compatibility ⟺
(log q)² ≲ log q/(4c) ⟺ log q ≲ 1/(4c). So the window is
nonempty only when log q ≤ 1/(4c)-grade — but the hypothesis
gives 1−β₁ < c/log q with q UNCONTROLLED above. THE HONEST
RESOLUTION: invoke the hypothesis at strength c″ := 1/(8·log q)…
circular. → The design DOWNGRADES the pre-adoption: the gate
adjudicates between (i′) the window in terms of 1−β₁ directly
(x ≤ exp(1/(4(1−β₁))): nonemptiness ⟺ (log q)²-grade ≤
1/(1−β₁), which the hypothesis DELIVERS by choosing
c := 1/(32·(log q...))) — NO: c is universally quantified FIRST.
Honest fix: restate the conclusion quantifiers — the theorem
should existentially produce (q, χ, β₁) AND the nonempty window
TOGETHER, invoking the hypothesis at a c′ chosen against a
DIAGONAL (for each n, c′ = 1/n gives data (qₙ, βₙ) with
1−βₙ < 1/(n·log qₙ); the window [exp(16(log qₙ+2)²),
exp(n·log qₙ/8... (1−βₙ)⁻¹ > n·log qₙ ⟹ cap
exp((n·log qₙ)/8) ⟹ nonemptiness ⟺ 16(log qₙ+2)² ≤ n·log qₙ/8
⟺ n ≥ 128(log qₙ+2)²/log qₙ — STILL q-dependent, but NOW the
theorem can DEMAND it: for each n take c′ = 1/n; if the produced
qₙ violates n ≥ 128(log qₙ+2)²/log qₙ, take a LARGER n′ =
⌈128(log qₙ+2)²/log qₙ⌉ and re-invoke — the hypothesis is ∀c∃,
so iterate: get q′ ≥ ... the produced q may CHANGE. The diagonal
terminates because at strength 1/n′ the data (q′, β′) satisfies
1−β′ < 1/(n′ log q′) and EITHER n′ ≥ 128(log q′+2)²/log q′
(done) or repeat; termination is NOT guaranteed — the q's may
grow forever. FINAL HONEST SHAPE (freeze this): make the
correlation statement PER-DATUM — a lemma about ANY exceptional
datum (q, χ, β₁) with 1−β₁ ≤ 1/(128·(log q+2)²·... the
q-adaptive strength), plus the top-level theorem quantified as:
∀ n, ∃ (data) with 1−β₁ < 1/(n·(log q+2)²) — i.e. the hypothesis
RESTATED at the q-adaptive rate, DERIVABLE from
InfinitelyManySiegelZeros? NO — ∀c∃ gives 1−β < c/log q; the
adaptive rate 1/(n(log q)²) does NOT follow (q floats).
**CONCLUSION OF THE HOUSE ANALYSIS: the na——**

## HOUSE VERDICT AT FREEZE-TIME (the III.3″ witness DID ITS JOB)

The symbolic witness computation above REFUTED the naive freeze
IN THE DESIGN DOCUMENT, before any gate or executor spend: the
∀c∃-shaped hypothesis (correct for HB-R1's dichotomy statement,
faithful to Tao Thm 1) does NOT by itself supply the
q-vs-(1−β₁) coupling that the correlation window needs — the
literature's Siegel-zero SEQUENCES carry ε_q = (1−β_q)·log q → 0
along a FIXED sequence of moduli, i.e. the coupling is part of
the hypothesis's intended reading, and HB 1983's proof uses
exactly that. TWO HONEST PATHS:
(P1) Strengthen the correlation core's hypothesis to the
     sequence form (define SiegelSequence : the ∃ of an infinite
     family (qₙ, χₙ, βₙ) with (1−βₙ)·log qₙ → 0 AND log qₙ₊₁ ≥
     (log qₙ)²-growth-freedom... just (1−βₙ)(log qₙ)² → 0 — the
     EXACT coupling the window needs), prove SiegelSequence →
     the per-datum correlation at every n, AND prove
     InfinitelyManySiegelZeros ↔ the weak form / SiegelSequence →
     InfinitelyManySiegelZeros (the one-way implication as the
     honesty bridge). HeathBrownStatement stays as-is (HB-R1's,
     untouched); the R2 core cites SiegelSequence and the
     writeup notes the two readings — this is ALSO what makes
     HB-R3+ honest later (HB 1983 consumes the sequence form).
(P2) Weaken the correlation conclusion to drop the residue-
     dominance clause (keep only the dichotomy approximation, no
     x²/3 separation) — closes from the plain hypothesis but
     loses the quantitative punch (the "silence" branch becomes
     indistinguishable).
**FROZEN DECISION: P1.** The gate's charges below are re-pointed
at the P1 shape; the SiegelSequence def + the one-way bridge
lemma join the frozen statements. (The full P1 statement block
is Appendix A of this doc, to be written by the gate-repair pass
if the gate confirms P1 — OR the gate may propose P1′ variants.)

## Nodes (post-P1)

| Node | Class | Content | Est. |
|---|---|---|---|
| HB2-a | B | SiegelSequence def + siegelSequence_implies_infinitely (the honesty bridge) + the III.3″ nonemptiness witness AS A THEOREM (∀ n large, the window at (qₙ, βₙ) is nonempty) | ~80k |
| HB2-b | C | corrWindow_box + residue_lower (log/sqrt/rpow arithmetic) | ~100k |
| HB2-c | C | The dichotomy core: SiegelSequence → the per-n correlation-or-silence (psi1_char_bound consumed; the β₁-identification via the box handled per the case table) | ~150k |

## Gate charge (adversarial, BEFORE executors)

1. **The P1 shape audit**: does SiegelSequence as the house
   defines it (Appendix A pending) genuinely deliver window
   nonemptiness for all large n (redo the symbolic arithmetic
   INDEPENDENTLY); is the one-way bridge to
   InfinitelyManySiegelZeros provable; is SiegelSequence faithful
   to the literature's "infinitely many Siegel zeros" (check Tao's
   blog + the HB paper's hypothesis as quoted in the B-R0 recon)?
2. **The β₁-identification**: in the window, is the hypothesis's
   zero THE dispatcher's exceptional zero (Page uniqueness —
   landau_one_exceptional_at's exact statement)? Or does the
   conclusion need the dispatcher's-own-β₁ restatement?
3. **Type/elaboration probe** (the HB1-gate discipline): scratch-
   elaborate the P1 statements; the NeZero/open/coercion corners.
4. **The residue arithmetic**: independently verify
   x^{β+1}/(β(β+1)) ≥ x²/3 under the P1 window.
5. **R4**: the core must NOT prove more than the dispatcher +
   hypothesis give (no branch selection smuggled); the docstrings
   carry the correlation-or-silence honesty + the HB-R3 door.
EOF
echo "frozen"
## POST-LANDING PROVENANCE NOTE (house, 2026-07-18 ~00:20)

The gate's APPENDIX A was delivered in its session report but
never persisted here — a house documentation gap the HB2 executor
correctly flagged. The executor RECONSTRUCTED the P1 block from
this doc's FROZEN DECISION + the ledger's gate summary; the house
(holding the gate report in-context) has performed the requested
review: **the reconstruction matches the gate's Appendix A in full
mathematical content**, with two cosmetic deviations, both
accepted: (i) SiegelSequence's final two conjuncts are in swapped
order; (ii) CorrWindow's cap is the multiplicative form
(1−β)·log x ≤ log(3/2) instead of the exp-quotient — equivalent
on the domain and division-free. THE LANDED FILE
(Salt/TwinBar/SiegelCorr.lean) IS NOW THE AUTHORITATIVE FORM of
Appendix A. Process rule reaffirmed: a gate whose verdict includes
authored statements must have those statements persisted to the
design doc AT ADJUDICATION TIME, not just the ledger summary.
