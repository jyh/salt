# S3-A-R2 DESIGN FREEZE — the entropy decrement lemma (Decrement)

**Status: FROZEN (house, 2026-07-17 ~23:40) — PENDING GATE.**
Provenance: the A-R0 ladder map (the ledger ~14:50; the recon's §2
is the authoritative annex — Lemma 3.1 read at page-image fidelity
from the PDF at the scratchpad, pp. 12/16/17/19–20; PDF numbering
authoritative). Consumer platform: A-R1 COMPLETE (the ledger
~23:10) — the (3.1)–(3.7) toolkit at both the R.V. and kernel
levels. THE BOUNDARY DECLARATION: this rung is the sprint's
registered depth probe — the first information-theoretic argument
in formalized analytic number theory; the acceptance rule is
relaxed per the registration (rungs are outcome classes; a death
here with the node map is a registered success).

## The mathematical object (Liouville spine, c_p = 1)

Tao 1509.05422 Lemma 3.1: on the log-sampled random integer
n ∈ (x/ω, x], the window pattern X_H = (λ(n+1), …, λ(n+H)) and
the residue datum Y_H = n mod P_H (P_H = ∏ of the primes in
(ε²H/2, ε²H]) satisfy, for SOME H ∈ [H₋, H₊] divisible by a:
  I[X_H : Y_H] ≤ H / (log H · log log log H).
The proof: IF the bound fails for every admissible H, the
concatenation subadditivity (3.11) H(X_{kH})/kH ≤ H(X_H)/H −
I(X_H,Y_H)/H + O(1/k) forces the entropy-per-symbol down by
≥ 1/(log H logloglog H) at every step of the tower
H_{j+1} = H_j·⌊C₀·log H_j·logloglog H_j⌋; the telescoped drop
Σ_j 1/(2Bj log j loglog(Bj log j)) diverges (barely) while the
entropy-per-symbol is bounded below by 0 — contradiction at a
finite J. Everything is finite probability + the landed toolkit;
NO external analytic input.

## THE MANDATORY REGIME STRUCTURE (the A-R0 D-risk mitigation)

Every parameter and every inter-parameter inequality lives in ONE
structure; every lemma of the rung is a field-to-field implication.
NO lemma may introduce a free parameter not drawn from the regime.

```lean
/-- The parameter regime of Tao 1509.05422 §3 (Liouville spine).
    The gate verifies the hypothesis list against pp. 16–20 page
    images; executors NEVER add fields or hypotheses — a missing
    inequality is a STOP-AND-FLAG (house re-freeze). -/
structure ChowlaRegime where
  x : ℕ           -- the outer scale
  ω : ℕ           -- the log-window width (n ∈ (x/ω, x])
  a : ℕ           -- the arithmetic-progression stride (H ≡ 0 mod a)
  eps : ℚ         -- the ε of the prime window (ε² scales 𝒫_H)
  Hlo Hhi : ℕ     -- the admissible H-range [H₋, H₊]
  C0 : ℕ          -- the tower ratio constant
  J : ℕ           -- the tower length
  hx : 2 ≤ x
  hω : 2 ≤ ω
  hωx : ω ≤ x
  ha : 1 ≤ a
  heps : 0 < eps
  heps1 : eps ≤ 1/2
  hHlo : a ≤ Hlo
  hHlohi : Hlo ≤ Hhi
  hC0 : 2 ≤ C0
  -- the tower fits the range and the sample window: FROZEN AS
  -- FIELDS after the gate's page-image pass pins the exact list
  -- (the recon recorded: H_j ≤ exp(B·j·log j); H₊ ≥ the J-step
  -- tower from H₋; x large enough that n + H₊ ≤ 2x-grade and
  -- the log-normalization Σ 1/n ∈ [log ω − 1, log ω + 1]).
  hHtower : True   -- PLACEHOLDER — the gate REPLACES this with the
                   -- verified field list; executors must not see
                   -- a placeholder (gate charge #1)
```

## Frozen Lean shapes — Salt/Entropy/Chowla/Decrement.lean tree
(new subtree Salt/Entropy/Chowla/; imports Salt.Entropy.Basic +
Salt.Entropy.Measure (+ Mathlib); NO .All)

```lean
/-- The log-sampling measure on (x/ω, x]: ℙ(n) ∝ 1/n. -/
noncomputable def logMeasure (x ω : ℕ) : Measure ℕ :=
  ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ≥0∞)⁻¹)⁻¹) •
    ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ≥0∞)⁻¹ • Measure.dirac n

instance : IsProbabilityMeasure (logMeasure x ω) -- (x/ω < x req.)
instance : FiniteSupport (logMeasure x ω)

/-- The Liouville window pattern. -/
def liouvilleWindow (H : ℕ) (n : ℕ) : Fin H → ℤ :=
  fun i => ArithmeticFunction.liouville (n + i + 1)

instance : FiniteRange (liouvilleWindow H)  -- range ⊆ {−1,1}^H

/-- The prime modulus P_H and the residue datum. -/
def primeWindow (eps : ℚ) (H : ℕ) : Finset ℕ := ...primesIn...
def PH (eps : ℚ) (H : ℕ) : ℕ := ∏ p ∈ primeWindow eps H, p
def residueWindow (eps : ℚ) (H : ℕ) (n : ℕ) : ZMod (PH eps H) := n

/-- THE HEADLINE (Lemma 3.1, Liouville). -/
theorem entropy_decrement (R : ChowlaRegime) :
    ∃ H : ℕ, R.Hlo ≤ H ∧ H ≤ R.Hhi ∧ R.a ∣ H ∧
      I[liouvilleWindow H : residueWindow R.eps H ;
          logMeasure R.x R.ω]
        ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))
```

(Executor latitude: measure-theoretic packaging (PMF vs Measure,
the ℝ≥0∞ coercions, the ZMod dependent-type handling of PH — a
sigma-type or a per-H fixed target may replace the dependent ZMod
if elaboration fights; the SHAPE of the four defs and the headline
inequality is frozen. THE AUTO-ETA BRIEF IS BINDING: v4.32 lacks
anonymous-constructor auto-eta over pi types — every joint variable
is written fun ω ↦ (X ω, Y ω), never ⟨X, Y⟩.)

## Node plan (waves; gate before wave I dispatches)

| Wave | Nodes | Class | Content | Est. |
|---|---|---|---|---|
| I | D-a, D-b, D-c | B | logMeasure + instances + the normalization facts (Σ1/n vs log ω, Mertens-style from the corpus); the window defs + FiniteRange/measurability; PH facts (incl. the EMPTY prime-window corner) | ~250k |
| II | D-d, D-e | **C** | the concatenation/shift analysis: X_{kH} vs the k shifted copies (the recon's flagged could-spike-D node — the approximate affine invariance under log-sampling; 2 attempts then a Fable design block per the recon) + the (3.8)–(3.10) inequalities | ~400k |
| III | D-f, D-g | C | (3.11) + the tower construction (H_j recursion in the regime) + the telescope | ~350k |
| IV | D-h | C | the barely-divergent series bound (numeric-flavored: partial-sum arithmetic at the regime's B, J) + the contradiction assembly → entropy_decrement | ~300k |

Total ~1.3M against the recon's 1.5–2.5M. Wave-I nodes are
parallel; II blocks on I; III on II; IV on III (a genuine chain —
the Zeno tripwire arms per chain as always).

## Case space (III.3‴ — the gate checks COMPLETENESS)

The empty prime window (ε²H ≤ 2: PH = 1, ZMod 1 trivial, I = 0 —
the bound holds trivially; enumerate, do not exclude) × the
H-multiple-of-a stepping (the tower must respect a ∣ H_j — check
Tao's "which is a multiple of a" carefully at the gate) × the
window overflow (n + H ≤ the sample range's headroom — the regime
carries the inequality) × x/ω floor arithmetic × k·H vs H₊ at the
tower top × the J-th step's existence (the ∃H is the NEGATION of
the all-H failure — mind the quantifier polarity in the
contradiction skeleton) × log log log H > 0 (H ≥ 16-grade floors
in the regime) × the deficient final block in concatenation
(X_{kH} covers [1,kH]; the last partial window).

## III.3″ witnesses (freeze artifacts)

(i) The tower arithmetic at concrete parameters (mpmath, in the
design record): C₀ = 2, H₀ = 10⁶: H_1 = 2·10⁶·⌊log·logloglog⌋…
the gate computes 10 steps and the partial sums of the
barely-divergent series, verifying the contradiction margin at
J ≈ the regime's bound. (ii) The normalization: at x = 10⁶,
ω = 10³: Σ_{n ∈ (10³,10⁶]} 1/n = 6.9077 ≈ log 10³ ✓ (mpmath).
(iii) The API smoke test: the consumer triple (3.1)/(3.5)/(3.7)
already compiles (A-R1's ConsumerTestRV) — the decrement's
toolkit is green by construction.

## Gate charge (adversarial, BEFORE wave I)

1. **The regime hypothesis list** (the transcribe-first pass):
   read pp. 16–20 of the PDF at the scratchpad as PAGE IMAGES and
   REPLACE the hHtower placeholder with the complete verified
   field list (every inequality the four waves consume). The
   placeholder reaching an executor is a NO-GO condition.
2. **The quantifier-polarity audit**: the headline is ∃H (the
   negation of ∀H-failure); the contradiction skeleton's polarity
   and the a ∣ H stepping through the tower — verify against the
   paper; the swat_vacuous precedent applies to the regime's
   bound directions.
3. **Elaboration probes**: logMeasure + the instances; the
   dependent ZMod (PH eps H) target (the known sharp corner —
   adjudicate sigma-type vs dependent); I[· : ·] at the landed
   API with the auto-eta rule.
4. **The witnesses**: run (i) and (ii) numerically; the tower must
   actually contradict at finite J with explicit margin.
5. **Case completeness** per the table; wave-II's could-spike-D
   flag protocol (2 attempts → Fable design block) restated in
   the wave-II briefs.
