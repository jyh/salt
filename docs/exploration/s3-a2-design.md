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

## WAVE-II GATE VERDICT (S3-A2-W2GATE, 2026-07-16) — **GO-WITH-BLOCK**

The node cut (D-d0 → D-d → D-e) STANDS. `hheadroom'` STANDS (C = 8,
p = 2; verified independently, 3.65× slack). Page images pp. 16–20
transcribed at fidelity; all five wave-II frozen shapes probe-elaborate
against `Salt.Entropy.All` (EXIT 0). Three blocks, all authored below —
NOT deferrals: (B1) D-d's frozen statement is the JOINT/CONDITIONAL
invariance, NOT the marginal (micro-freeze §1 architecture note was
incomplete — corrected here); (B2) a new normalizer-floor helper
`logMeasure_norm_ge_half` (the log-lower-bound of `harmonic_window_bounds`
is vacuous for ω ≤ e, but the invariance ℓ¹ needs a positive Σ floor);
(B3) the difficulty spike is D-d0 (elementary Fannes), NOT the arithmetic
— extend the 2-attempts-then-Fable-block protocol to D-d0 as well.

### Charge 1 — the (3.8)–(3.11) fidelity pass (pp. 17–20, verbatim)

Transcribed inequalities (Tao 1509.05422, PDF pp. 17–20):
- (3.8) `0 ≤ ℍ(X_H) ≪_ε H`. (3.9) `ℍ(Y_H) = log P_H − o_{A→∞}(1)`.
  (3.10) `ℍ(Y_H) ≪ H` for `H₋ ≤ H ≤ H₊` (from PNT).
- p.18 concatenation heart: `X_{H₁,H₁+H₂}` = window on the SHIFTED block
  `[H₁+1, H₁+H₂]` of the SAME `n`. Lemma 2.5 (approx. translation
  invariance): `ℍ(X_{H₁,H₁+H₂}) = ℍ(X_{H₂}) + o_{A→∞}(1)`; subadditivity
  (3.4) then gives `ℍ(X_{H₁+H₂}) ≤ ℍ(X_{H₁}) + ℍ(X_{H₂}) + o(1)`.
- The MI improvement (p.18, the load-bearing step): the CONDITIONAL
  invariance `ℍ(X_{H₁,H₁+H₂} | n+H₁(P_H)) = ℍ(X_{H₂} | n(P_H)) + o(1)`
  PLUS the exact σ-algebra relabel (`n+H₁ (P_H)` and `n (P_H)` generate
  the same σ-algebra) yields the RELATIVE subadditivity
  `ℍ(X_{H₁+H₂}|Y_H) ≤ ℍ(X_{H₁}|Y_H) + ℍ(X_{H₂}|Y_H) + o(1)`, iterated to
  `ℍ(X_{kH}|Y_H) ≤ k·ℍ(X_H|Y_H) + o(1)`.
- (3.11) p.19, VERBATIM: `ℍ(X_{kH})/kH ≤ ℍ(X_H)/H − 𝕀(X_H,Y_H)/H + O(1/k)`,
  for `H₋ ≤ H ≤ kH ≤ H₊`, from
  `ℍ(X_{kH}) ≤ k·ℍ(X_H|Y_H) + ℍ(Y_H) + o(1) = k·ℍ(X_H) − k·𝕀(X_H,Y_H) + ℍ(Y_H) + o(1)`
  (uses (3.1),(3.3),(3.5)) divided by `kH`.

Recon confirmations: the **O(1/k) source IS `ℍ(Y_H)/(kH)`** and Dc's
`log_PH_le` (`log P_H ≤ ε²H·log 4`) feeds it correctly — via (3.7)
`ℍ(Y_H) ≤ log P_H ≤ ε²H·log 4`, so `ℍ(Y_H)/(kH) ≤ ε²·log4/k = O_ε(1/k)`.
The MI term enters at the conditional-subadditivity step, converted to
`ℍ(X_H) − 𝕀` by (3.5).

**DIVERGENCE (B1).** Micro-freeze §1 says invariance enters "ONLY in
`H[X_H^{(j)}] ≈ H[X_H^{(0)}]`" (MARGINAL). This is INSUFFICIENT: the
`−𝕀/H` decrement — the whole point of Lemma 3.1 — requires the CONDITIONAL
subadditivity `ℍ(X_{kH}|Y_H) ≤ Σ_j ℍ(X_H^{(j)}|Y_H)` (invariance-free,
good — derivable from `entropy_triple_add_entropy_le` + `chain_rule`)
FOLLOWED BY the CONDITIONAL invariance `ℍ(X_H^{(j)}|Y_H) ≈ ℍ(X_H|Y_H)`.
The marginal invariance does not produce the MI gain. FIX: D-d is the
JOINT-law invariance `|ℍ(X_H^{(j)},Y_H) − ℍ(X_H,Y_H)| ≤ err_j`; the
conditional gap EQUALS the joint gap (the common `ℍ(Y_H)` cancels — same
μ, same Y_H), and the joint reduces to the SAME ℓ¹ estimate via the exact
σ-algebra relabel of the residue coordinate `r ↦ r + jH (mod P_H)`
(bijection). Concretely `ℍ(X_H^{(j)},Y_H;μ) = ℍ(X_H,Y_H; (T_{jH})_*μ)`,
so the gap is `≤ Fannes(TV((T_{jH})_*μ, μ))` on the JOINT range
`(Fin H→ℤ)×ZMod P_H` (card `≤ 2^H·P_H`, `log ≤ (3/2)·H·log 2` since
`ε²·log4 ≤ ½·log2` for `ε ≤ ½`). Otherwise the same-measure /
shifted-function architecture IS Tao's `X_{H₁,H₁+H₂}` structure faithfully;
Tao's `o_{A→∞}(1)` is replaced by the EXPLICIT Fannes error governed by
`hheadroom'` (the flagged-missing A-parameter → explicit inequality).

### Charge 2 — the invariance-arithmetic REDO (the kill-check)

Let `μ = logMeasure x ω`, window `W = (m₀, x]`, `m₀ = x/ω`,
`Σ = Σ_{n∈W} 1/n`, `ν = (T_{jH})_*μ` (mass `1/(m−jH)` at `m∈(m₀+jH, x+jH]`).
Splitting `‖μ−ν‖₁` into left-edge `A = Σ_{m₀<m≤m₀+jH} 1/m`, overlap
`B = Σ_{m₀+jH<m≤x}(1/(m−jH)−1/m)`, right-edge (the "reads past x" defect)
`C = Σ_{x−jH<n≤x} 1/n`: the overlap telescopes **exactly** to `B = A − C`,
so

>  **ℓ¹(law X_H^{(j)}, law X_H) ≤ ‖ν−μ‖₁ = 2A_j/Σ**,   `A_j = Σ_{m₀<m≤m₀+jH} 1/m`.

(Verified exactly at four `(x,ω,jH)` instances, `|ℓ¹ − 2A/Σ| ~ 1e-17`.)
Robust floors (no ω-largeness needed): `Σ ≥ 1 − 1/ω ≥ 1/2` (each `1/n ≥ 1/x`,
`|W| = x − m₀ ≥ x − x/ω`) and `m₀ ≥ x/(2ω)` ⟹
`d_j := 2A_j/Σ ≤ 8·jH·ω/x`, hence `d_max ≤ 8·Hhi·ω/x` (using `kH ≤ Hhi`).
Joint-Fannes error `err_j = d_j·(3/2)H·log2 + binEntropy(d_j)`; in (3.11) the
total error is `(Σ_{j<k} err_j)/(kH) ≤ err_max/H` (the H cancels in the
leading term):

>  leading `E ≤ (3/2)log2·d_max ≤ 12·log2·Hhi·ω/x`;  need `E ≤ 1/(4·logH·logloglogH)`
>  (worst at `H = Hhi`)  ⟺  **`x/ω ≥ 48·log2·Hhi·logHhi·logloglogHhi`**.

At the floor `Hhi = Hlo = 4·10⁶`: `logHhi = 15.20`, `logloglogHhi = 1.001`;
needed `x/ω ≥ 2.02·10⁹`. **Frozen `hheadroom'` `= 8·Hhi·(logHhi)² = 7.40·10⁹`
≥ 2.02·10⁹ → 3.65× slack.** The `binEntropy(d_max)` correction: `d_max ≤
1/(logHhi)² = 4.3·10⁻³ ≪ 1/e = 0.368`, `binEntropy(d_max) ≈ 0.028`, so
`binEntropy(d_max)/H ≤ 7·10⁻⁹` vs budget `1/(4·logHhi·logloglogHhi) = 0.0164`
— 6+ orders negligible. **C = 8, p = 2 PINNED, no retune.** (The `O(1/k)`
term `ℍ(Y_H)/(kH) ≤ ε²log4/k` is handled at the tower step, wave III, by
`k = ⌊C₀ logH logloglogH⌋` with `C₀` large.)

### Charge 3 — D-d0 adjudication

mathlib has NO Fannes and NO half-built entropy modulus-of-continuity;
`NegMulLog` supplies continuity/`concaveOn_negMulLog`/`negMulLog_le_one_sub_self`/
`negMulLog_mul`, `BinaryEntropy` supplies `Real.binEntropy` (+ concavity,
`binEntropy_le_log_two`, `binEntropy_eq_negMulLog_add_negMulLog_one_sub`,
monotone on `[0,½]`), and `Measure.lean` supplies the finite-sum expansion
`measureEntropy_of_isProbabilityMeasure_finite`. So D-d0 is genuinely new.
Honest form = ℓ¹-Fannes over a **SUPPORT FINSET** (`A.card`, NOT `Fintype.card`
— the window codomain `Fin H → ℤ` is infinite). The frozen bound
`|Hm[μ] − Hm[ν]| ≤ d·log(A.card) + binEntropy d` (`d = ℓ¹`, `d ≤ 1/e`) is a
SAFE over-estimate of the sharp Fannes–Audenaert `T·log(N−1) + binEntropy T`
(`T = d/2`): `d·log(A.card) ≥ (d/2)log(A.card−1)` and `binEntropy d ≥
binEntropy(d/2)` for `d ≤ ½` — hence TRUE, and (Charge 2) sufficient. Its
PROOF (the `S₋`-straddle coupling) is the real wave-II spike → B3.

### Charge 4 — quantifier / case audit

- **j = 0 identity**: `liouvilleWindowShift H 0 = liouvilleWindow H` (PROVEN
  in probe, not sorry); `A_0 = 0 ⟹ d_0 = 0 ⟹ err_0 = 0`.
- **edge windows `n + kH > x`**: `ArithmeticFunction.liouville` is TOTAL, so
  the pattern is well-defined — NO domain corner. The LAW edge is exactly
  region `C` (right-edge defect), fully inside the `2A/Σ` accounting.
- **h(d) domain `d ≤ 1/e`**: frozen as `Real.exp (-1)`; `d_max ≈ 4.3·10⁻³ ≪
  1/e` (huge margin).
- **`k·H ≤ Hhi` coupling**: max shift `(k−1)H < kH ≤ Hhi` (regime `hfit`);
  used in `d_max ≤ 8Hhiω/x`. MUST be a D-d/D-e hypothesis (`k*H ≤ R.Hhi`).
- **ℓ¹-vs-TV factor 2**: pinned — `d = ℓ¹ = 2·TV`, `TV = A/Σ`; D-d0 takes ℓ¹.
- ∃H polarity / `a ∣ H` stepping: unchanged from wave I; wave II is the
  per-step (3.11), introduces no new quantifier.

### Charge 5 — the wave-II FROZEN STATEMENTS (verbatim-ready; all probe-EXIT-0)

New subtree `Salt/Entropy/Chowla/Decrement.lean` (+ `ChowlaRegime` field
`hheadroom'`). Notation from `Salt.Entropy.Basic`/`Measure`. AUTO-ETA rule
binding: every joint variable is `fun n ↦ (X n, Y n)`, never `⟨X, Y⟩`.

```lean
-- Regime field to ADD (replaces the wave-I `hheadroom` deferral):
--   hheadroom' : 8 * (Hhi : ℝ) * Real.log Hhi * Real.log Hhi ≤ ((x / ω : ℕ) : ℝ)

/-- The shifted window X_H^{(j)} n := liouvilleWindow H (n + j·H).  (FiniteRange +
    measurability PROVEN in the gate probe, not sorry; j = 0 gives liouvilleWindow H.) -/
def liouvilleWindowShift (H j : ℕ) (n : ℕ) : Fin H → ℤ := liouvilleWindow H (n + j * H)

instance instFiniteRangeShift (H j : ℕ) : FiniteRange (liouvilleWindowShift H j) :=
  finiteRange_of_finset (liouvilleWindowShift H j)
    (Fintype.piFinset (fun _ : Fin H => ({-1, 1} : Finset ℤ)))
    (fun n => liouvilleWindow_mem_piFinset H (n + j * H))

lemma measurable_liouvilleWindowShift (H j : ℕ) : Measurable (liouvilleWindowShift H j) :=
  measurable_of_countable _

/-- **D-d0** (elementary ℓ¹-Fannes; support-Finset card, NOT Fintype.card).
    Honest form; SAFE over-estimate of sharp Fannes–Audenaert. PROOF = the spike (B3). -/
theorem entropy_sub_le_of_l1
    {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Finset S) (hμ : μ Aᶜ = 0) (hν : ν Aᶜ = 0)
    (d : ℝ) (hd : d = ∑ s ∈ A, |μ.real {s} - ν.real {s}|)
    (hd1 : d ≤ Real.exp (-1)) :
    |Hm[μ] - Hm[ν]| ≤ d * Real.log (A.card : ℝ) + Real.binEntropy d

/-- **B2 helper**: the robust positive normalizer floor (harmonic_window_bounds'
    log-floor is vacuous for ω ≤ e; the invariance ℓ¹ needs Σ ≥ 1/2). -/
theorem logMeasure_norm_ge_half {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) :
    (1 : ℝ) - 1 / (ω : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹
-- corollary consumed by D-d:  (1:ℝ)/2 ≤ Σ  (since ω ≥ 2).

/-- **D-d** (the JOINT/CONDITIONAL invariance — B1).  Mathematical content:
    the conditional gap = joint gap = Fannes(2A_j/Σ) on the joint range
    (D-d0 with A = piFinset{-1,1} ×ˢ (ZMod P_H).univ, card ≤ 2^H·P_H), and
    2A_j/Σ ≤ 8·j·H·ω/x (Charge 2).  Consumable bound delivered to D-e (per
    shift, uniform in j via k·H ≤ Hhi + hheadroom'): -/
theorem condEntropy_shift_le (R : ChowlaRegime) {H k j : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : k * H ≤ R.Hhi) (hj : j < k) (ha : R.a ∣ H) :
    H[liouvilleWindowShift H j | residueWindow R.eps H ; logMeasure R.x R.ω]
      ≤ H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
        + (H : ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H)))

/-- **D-e** (the (3.8)–(3.10) inputs + the (3.11) per-step assembly).  Keeps the
    TWO errors explicit: ℍ(Y_H)/(kH) ≤ ε²·log4/k  (the O(1/k)); and the Fannes
    1/(4·logH·logloglogH).  Wave-III (D-f) substitutes k = ⌊C₀ logH logloglogH⌋ to
    fuse them into the clean −1/(2 logH logloglogH) tower step. -/
theorem step_ineq_3_11 (R : ChowlaRegime) {H k : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : k * H ≤ R.Hhi) (ha : R.a ∣ H) (hk : 1 ≤ k) :
    H[liouvilleWindow (k * H) ; logMeasure R.x R.ω] / ((k : ℝ) * H)
      ≤ H[liouvilleWindow H ; logMeasure R.x R.ω] / (H : ℝ)
        - I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] / (H : ℝ)
        + ((R.eps : ℝ) ^ 2 * Real.log 4) / (k : ℝ)
        + 1 / (4 * Real.log H * Real.log (Real.log (Real.log H)))
```

D-e assembly skeleton (all pieces landed except D-d): (1) `ℍ(X_{kH}) =
ℍ(X_H^{(0)},…,X_H^{(k-1)})` via `liouvilleWindow_block` + `entropy_comp_of_injective`
(the `finProdFinEquiv` reindex); (2) `ℍ(X_{kH}) ≤ ℍ(Y_H) + ℍ(X_{kH}|Y_H)`
(`chain_rule'` + `condEntropy_nonneg`); (3) conditional subadditivity iterated
(from `entropy_triple_add_entropy_le` + `chain_rule` — a helper lemma,
invariance-free); (4) D-d per shift; (5) `mutualInfo_eq_entropy_sub_condEntropy`;
(6) `entropy_residueWindow_le_log_PH` + `log_PH_le`. Divide by `kH`.

**Dispatch note**: D-d0 first (spike; Fable-block if the coupling stalls at
2 attempts), then B2 helper (trivial), then D-d (B1 joint form), then D-e.
Executor latitude on err-term packaging (per-shift-uniform vs summed) is open;
the SHAPES above and `hheadroom'` are frozen.
