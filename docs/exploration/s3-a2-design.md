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
  -- ==== GATE-VERIFIED FIELD LIST (S3-A2-GATE, pp. 11–20 page images;
  --      replaces the hHtower placeholder; whole structure elaborates,
  --      EXIT 0). chowlaTower / towerDropSum are the two prerequisite
  --      defs added to the Frozen Lean shapes below. ====
  hHlo_floor : 4000000 ≤ Hlo   -- H₋ ≥ e^{e^e} ≈ 3.814·10⁶: forces
                               -- logloglog H₋ ≥ 1, hence the tower step
                               -- ⌊C₀·logH·logloglogH⌋ ≥ 2 (STRICT growth)
                               -- and the decrement 1/(2 logH logloglogH) > 0.
                               -- CATCH: the freeze/recon "H ≥ 16-grade floor"
                               -- STALLS the tower — at H = 16 the floor is 0
                               -- (logloglog 16 = 0.0196; C₀=2 ⇒ ⌊2·2.77·0.02⌋=0).
                               -- Minimal non-stall (C₀=2) is H ≳ 45; 4·10⁶ is the
                               -- clean choice that also gives logloglog ≥ 1.
  hheadroom  : Hhi ≤ x / ω     -- MINIMAL headroom (necessary, likely NOT
                               -- sufficient). p.11's true hierarchy is far
                               -- stronger: a,b,h ≪ 1/ε ≪ H₋ ≪ H₊ ≪ A ≤ ω ≤
                               -- x/log x ≤ x AND x/ω ≥ log A ≫ H₊, i.e.
                               -- H₊ ≪ log A ≤ log ω (ω is EXPONENTIALLY larger
                               -- than H₊). GATE FLAG: the o_{A→∞}(1)-governing
                               -- parameter A is MISSING from the regime; Lemma
                               -- 2.5's (Wave II) affine-invariance error control
                               -- needs it (or ω ≥ e^{Hhi}-grade). DEFER the exact
                               -- headroom/A field to a Wave-II micro-freeze once
                               -- the o_{A→∞} error-formalization route is chosen
                               -- (this is the flagged could-spike-D node).
  hcoprime   : (a : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) / 2
                               -- P_H coprime to a (p.16): every prime of 𝒫_H
                               -- exceeds ε²H/2 ≥ ε²H₋/2 ≥ a. SETUP-faithful; NOT
                               -- consumed by the entropy proof of Lemma 3.1 (it is
                               -- used upstream in Prop 2.6). Drop only if the rung
                               -- proves entropy_decrement in isolation.
  hfit       : chowlaTower C0 a Hlo J ≤ Hhi
                               -- "H₊ sufficiently large depending on H₋, C₀, J"
                               -- (p.19): the J-step tower fits below H₊; with
                               -- monotonicity ⇒ every H_j ∈ [H₋, H₊].
  hJcon      : Real.log 2 < towerDropSum C0 a Hlo J
                               -- "J sufficiently large depending on C₀, H₋, ε"
                               -- (p.20): the telescoped decrement Σ exceeds the
                               -- Liouville entropy ceiling ℍ(X_H)/H ≤ log 2,
                               -- forcing the contradiction. NB the (barely-)
                               -- divergence proof is RELOCATED to regime-
                               -- instantiation (proving ∃ ChowlaRegime). The
                               -- crossing J is astronomically large (at J = 10⁷
                               -- the sum is still 0.489 < log 2 = 0.693): Wave IV
                               -- must formalize SERIES DIVERGENCE, not a finite
                               -- numeric margin.
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
def primeWindow (eps : ℚ) (H : ℕ) : Finset ℕ := ...primesIn...  -- ε²H/2 < p ≤ ε²H
def PH (eps : ℚ) (H : ℕ) : ℕ := ∏ p ∈ primeWindow eps H, p
def residueWindow (eps : ℚ) (H : ℕ) (n : ℕ) : ZMod (PH eps H) := (n : ZMod (PH eps H))

-- GATE (charge #3b): PH ≥ 1 ALWAYS (empty product = 1; primes ≥ 2). Register
-- this NeZero instance globally; then the DEPENDENT ZMod (PH eps H) target
-- elaborates and FiniteRange / MeasurableSingletonClass / Countable / Fintype
-- (for entropy_le_log_card ⇒ ℍ(Y_H) ≤ log|ZMod PH| = log PH) all resolve — no
-- sigma-type, no fixed-ambient-ℤ encoding needed. (Gate-probed, EXIT 0.)
instance (eps : ℚ) (H : ℕ) : NeZero (PH eps H) := ⟨by
  have : 0 < PH eps H := Finset.prod_pos (fun p hp => (by
    simp only [primeWindow, Finset.mem_filter] at hp; exact hp.2.1.pos)); omega⟩

/-- The tower recursion (Lemma 3.1, p.19): H₁ = a·H₋ (index 0),
    H_{j+1} = H_j·⌊C₀ log H_j logloglog H_j⌋. GATE-verified to elaborate. -/
noncomputable def chowlaTower (C0 a Hlo : ℕ) : ℕ → ℕ
  | 0     => a * Hlo
  | (j+1) => chowlaTower C0 a Hlo j *
      ⌊(C0 : ℝ) * Real.log (chowlaTower C0 a Hlo j : ℝ)
        * Real.log (Real.log (Real.log (chowlaTower C0 a Hlo j : ℝ)))⌋₊

/-- The telescoped per-step entropy decrement Σ_{j<J} 1/(2 log H_j logloglog H_j). -/
noncomputable def towerDropSum (C0 a Hlo J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J,
    1 / (2 * Real.log (chowlaTower C0 a Hlo j : ℝ)
           * Real.log (Real.log (Real.log (chowlaTower C0 a Hlo j : ℝ))))

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

## WAVE-II MICRO-FREEZE (house, 2026-07-18 ~03:40) — the deferred
## A-parameter headroom + the concatenation architecture

1. **Architecture (frozen):** the SAME-measure, SHIFTED-FUNCTION
   formulation. All windows live on ONE logMeasure; X_H^{(j)} n :=
   liouvilleWindow H (n + j*H) (Db's liouvilleWindow_block is the
   splitting). Subadditivity (entropy_pair_le_add iterated) needs
   NO invariance. Approximate invariance enters ONLY in
   H[X_H^{(j)}] ≈ H[X_H^{(0)}]: the law of X_H^{(j)} is the
   pushforward of logMeasure under a jH-shift — multiplicatively
   (1+δ)-close on the common window (mass ratio m/(m−jH)) plus
   edge defect η, with δ + η ≲ Hhi·ω/x + Hhi/((x/ω)·log ω).
2. **The new library node D-d0 (B/C):** the entropy-comparison
   lemma — for μ, ν on a finite range S with ℓ¹ distance d:
   |Hm[μ] − Hm[ν]| ≤ d·log|S| + (the concave h(d) term) (discrete
   Fannes; or the ratio form if cheaper). NEW to the ported
   library; the wave-II gate adjudicates the exact form.
3. **The regime strengthening (replaces the gate's deferral):**
   `hheadroom' : 8 * (Hhi : ℝ) * Real.log Hhi * Real.log Hhi ≤
   ((x / ω : ℕ) : ℝ)` — the shape: the per-shift ℓ¹ error times
   H·log 2 (Fannes at |S| ≤ 2^H) must stay below half the per-step
   decrement 1/(2 log H logloglog H). Witness at the floor
   (Hlo = Hhi-grade = 4·10⁶): 8·4e6·(15.2)² ≈ 7.4e9 ≤ x/ω — sane
   (x ≥ exp-tower anyway per hJcon's J). THE WAVE-II GATE REDOES
   this arithmetic independently (the HB2 precedent) and may
   retune the constant/log-powers; the FIELD SHAPE is frozen.
4. Case table addition: the j = 0 identity case × the edge windows
   (n + kH > x) × the ℓ¹-vs-TV factor 2 × h(d)'s domain (d ≤ 1/e).
5. Wave-II nodes: D-d0 (Fannes, B/C ~120k) → D-d (the invariance
   estimate, C ~150k) → D-e (the (3.8)–(3.10) inequalities +
   (3.11) assembly, C ~150k). The 2-attempts-then-Fable-block
   protocol on D-d and D-e (the could-spike-D pair).
