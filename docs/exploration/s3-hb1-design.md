# S3-HB-R1 DESIGN FREEZE — the Heath-Brown statement (SiegelTwin)

**Status: FROZEN (house, 2026-07-17 ~15:55) — PENDING GATE.**
Provenance: S3-B-R0 (PLACEABLE-NARROWED; the checkpoint SPLIT, JYH
"agreed"). Primary: Tao 2015 ("Heath-Brown's theorem on prime twins
and Siegel zeroes"), Theorem 1; HB 1983 PLMS for provenance only
(the qualitative target is constant-free — the effective constants
are NOT frozen here and carry the recon's extraction-risk flag).

## Frozen Lean statements — Salt/TwinBar/SiegelTwin.lean
(imports: Salt.SW.Siegel (or the module carrying LFunction + the
primitive-quadratic shape — executor verifies) + Salt.Basic;
NO .All)

```lean
/-- NO Siegel zeros: some c > 0 pushes every real primitive
    character's real zeros below 1 − c/log q.  (Tao Thm 1 (ii).) -/
def NoSiegelZeros : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q,
    1 < q → χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
    ∀ β : ℝ, LFunction χ β = 0 → β < 1 →
      β ≤ 1 - c / Real.log q

/-- Infinitely many Siegel zeros — the ¬NoSiegelZeros unfolding,
    stated POSITIVELY in the ∀c∃ order (the witness AFTER c; the
    ∃∀ order is provably FALSE — the swat_vacuous trap, banned). -/
def InfinitelyManySiegelZeros : Prop :=
  ∀ c : ℝ, 0 < c → ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (β : ℝ),
    1 < q ∧ χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
    LFunction χ β = 0 ∧ 1 - c / Real.log q < β ∧ β < 1

/-- The Heath-Brown 1983 statement (qualitative form). -/
def HeathBrownStatement : Prop :=
  InfinitelyManySiegelZeros → TwinPrimeConjecture

/-- The dichotomy corollary shape. -/
def HeathBrownDichotomy : Prop :=
  TwinPrimeConjecture ∨ NoSiegelZeros
```

Required lemmas (all in-file, sorry-free — this rung lands as
Props + PROVEN glue, the Brun.BrunStatement pattern):
1. `noSiegelZeros_iff_not_infinitely` — the two Props are exact
   negations (Classical push_neg bookkeeping; the freeze's ∀c∃ vs
   ∃∀ discipline is CHECKED by this lemma existing).
2. `heathBrown_iff_dichotomy` — HeathBrownStatement ↔
   HeathBrownDichotomy (propositional).
3. **Non-vacuity guards (III.3″, both directions):**
   a. `badHyp_false` — the ∃∀ mis-freeze
      (∃ q χ β, ... ∧ ∀ c > 0, 1 − c/log q < β) is FALSE
      (as β < 1 while c → 0 forces β ≥ 1) — the trap exhibited as
      a theorem, per the B-R0 mandate.
   b. `infinitelyMany_not_refuted` — a PROSE docstring note (not a
      theorem): the corpus does not decide InfinitelyManySiegelZeros
      (zero_free_region_all carves out exactly this zero;
      siegel_theorem is ineffective by design) — cite both.
4. `siegel_gap_lower` (anti-triviality): from the LANDED
   siegel_theorem/goldfeld machinery, every such β satisfies
   β ≤ 1 − C(ε)/q^ε ineffectively — i.e. the hypothesis asserts
   something GENUINELY between Landau–Page and Siegel; state the
   cheap direction if it is cheap, else prose.

## The R4 docstring frame (MANDATED, verbatim content from B-R0)

The module docstring MUST carry: (1) "conditional on
InfinitelyManySiegelZeros, believed FALSE"; (2) the
non-contradiction triple vs the wall — tolerant-certificate
blindness vs character-sightedness; MmuRate is ζ-governed and
remains TRUE under the hypothesis (different L-function); the
corpus deliberately carves out the exceptional zero — with explicit
cross-references to no_parity_beating_certificate_unconditional
and zero_free_region_all; (3) the hypothesis-form discipline note.

## Case space (III.3‴)

The quantifier-order pair (∀c∃ vs ∃∀ — one live, one refuted in-
file) × the β = 1 boundary (excluded: LFunction_apply_one_pos) ×
q ≤ 1 (excluded by 1 < q) × χ non-primitive/non-quadratic
(excluded by hypotheses) × the ε-fixed Landau–Page confusion
(documented as the WEAKER regime, non-equivalent) × ℂ vs ℝ
character coercion (match Siegel.lean:232's exact types).

## Nodes

| Node | Class | Content | Est. |
|---|---|---|---|
| HB1-a | B/C | The four Props + lemmas 1, 2, 3a (the statement file) | ~120k |
| HB1-b | B | The R4 docstrings + lemma 4 (or its prose form) + wiring | ~60k |

HB-R2 (the μ↔χ correlation core) freezes SEPARATELY after HB-R1
lands and its gate clears — its recon-priced inputs
(psi1_char_bound, the MVT bridges, goldfeld_L_one_lower) are
landed; the design question is the correlation statement's exact
carrier.

## Gate charge

(1) The quantifier audit (the trap lemma 3a actually refutes the
bad form; the live form matches Tao Thm 1 (ii)'s negation
exactly); (2) type-fidelity vs Siegel.lean:227–232 (the corpus's
canonical primitive-quadratic spelling — byte-level); (3) the
non-vacuity prose citations exist as claimed; (4) R4 frame
completeness; (5) LFunction vs mathlib's DirichletCharacter
LFunction at real arguments — the β : ℝ coercion corner.

## GATE VERDICT (2026-07-17 ~17:30): GO-WITH-AMENDMENTS — applied

S3-HB1-GATE (≈ 99k / 23 tools; two scratch probes BUILD EXIT 0 —
the gate PROVED the negation lemma, the dichotomy iff, and
badHyp_false in-probe). Charges: quantifier audit PASS (the ≤/<
pairing is exactly right — the boundary belongs to the same side
in both Props); Tao Thm 1 match PASS (+ A5: the closed-interval
endpoint nuance, absorbed by the existential c — docstring note);
citations PASS (the carve-out at ZeroFreeReal.lean:605-608 is
literally (χ² ≠ 1 ∨ im ≠ 0); siegel_theorem's q^ε gap is WEAKER
than the log-q gap, so the corpus genuinely does not decide the
hypothesis); R4 PASS (the MmuRate ζ-vs-L(χ) honesty verified at
the proof spine); β-semantics PASS (real-axis pinned, no off-axis
admission). AMENDMENTS (elaboration, all build-verified): A1/A2
the [NeZero q] binders + open Complex DirichletCharacter (the
freeze dropped both vs Siegel.lean:228/231); A3 BadHyp same; A4
push Not (push_neg deprecated in this mathlib); A5 the endpoint
note. The corrected frozen block + proven lemma bodies are IN the
gate report (the executor lifts them verbatim). HB1-EXEC
dispatches (single executor — the gate pre-proved the hard glue).
