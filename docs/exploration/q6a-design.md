# Q6a DESIGN — the parity wall as an interface theorem (Fable freeze, pre-gate)

*2026-07-15, REVISED post-gate (all three mandatory corrections + the amendment applied — the gate report is in the exploration ledger). From the Q6a-recon (the pilot ledger): the honest shape is
the consumer-relative form (c) with the ε-agreement core (b); the
exact-agreement shapes are vacuous. This design freezes the statements
for the gate. The corpus convention (EHall/PiAsymp-style named Props)
carries the analytic input; the unconditional Σλ discharge is a stretch
sub-node.*

## D1 — the sifting instances (the Selberg witness pair)

Over `support = Icc 1 x` (as the sieve's ℕ-support), `prodPrimes = P(z) =
∏_{p ≤ z} p` at `z = Nat.sqrt x` (GATE CORRECTION 1: ≤ not < — the strict
form lets z² survive whenever z is prime, falsifying siftedSum₊ = 2 on an
unbounded set; verified at x = 25/49/169), shared density `ν(d) = 1/d`
(`nuDiv : ArithmeticFunction ℝ`, the integer-sifting density — NOT
nuChen; multiplicativity and 0 < ν(p) < 1 for p ≥ 2 are elementary),
shared `totalMass = (x : ℝ)`:

- `sPlus x`: `weights n = 1 + (liouville n : ℝ)` (mathlib's
  `ArithmeticFunction.liouville`, cast; `weights_nonneg` from λ ∈ {±1}).
- `sMinus x`: `weights n = 1 − (liouville n : ℝ)`.

Evaluations (elementary, z = √x):
- `siftedSum (sPlus x) = 2` — survivors coprime to P(√x) in [1, x] are
  {1} ∪ primes(√x, x]; 1 + λ(1) = 2; 1 + λ(p) = 0.
- `siftedSum (sMinus x) = 2·(π(x) − π(√x))` — the prime mass, doubled.
- Prime powers p^k (k ≥ 2, p > √x) exceed x — none survive; state and
  use this.

## D2 — the Agree relation (what the sieve consumes)

```
def SieveAgree (s t : BoundingSieve) (D : ℕ) (B : ℝ) : Prop :=
  s.prodPrimes = t.prodPrimes ∧ s.nu = t.nu ∧ s.totalMass = t.totalMass
  ∧ rosserRemainder s D ≤ B ∧ rosserRemainder t D ≤ B
```
Rationale (the recon's consumed-field enumeration): every landed main
term reads ONLY {prodPrimes, nu, totalMass}; the error term reads
support/weights only through `Σ_{d<D} |rem d|`. Exact equality on the
main-fields, a shared budget on the remainder — the exact granularity
the interface operates at.

## D3 — the analytic input (GATE AMENDMENT: no λ-BV — the summatory rate suffices; the wall is UNCONDITIONAL)

Total multiplicativity gives the POINTWISE identity
`Σ_{n≤x, d∣n} λ(n) = λ(d)·M_λ(⌊x/d⌋)` — the a = 0 class never needs
equidistribution. The analytic input shrinks to the effective summatory
rate `LambdaSummatory A : |M_λ(y)| ≤ C·y/(log y)^A`, SOURCED FROM THE
LANDED `siegelWalfisz_psiTot` via two bridge nodes (Q6a-3, now
CRITICAL-PATH not stretch): (i) ψ→M_μ (the Tauberian bridge at the
power-log rate), (ii) M_μ→M_λ (λ = μ∗1_squares, the hyperbola fold —
rate-preserving since x/d² ≥ ... with log(x/d) ≥ log x/2 on the range).
The rem bound: |rem d| ≤ 1 + |M_λ(⌊x/d⌋)|; summed over d ∣ P(z), d < D
with Σ1/d ~ log x: rosserRemainder ≤ C·x/(log x)^A at A-2. (The old
LambdaLevel λ-BV design is RETIRED — kept below for the record only.)

## D3-RETIRED — the named-Prop λ-BV route (superseded by the amendment)

```
def LambdaLevel (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 ≤ B ∧ ∀ x : ℕ, 2 ≤ x →
    (∑ d ∈ Icc 1 ⌊(x:ℝ)^θ / (log x)^B⌋₊,
        (⨆-style max over residues a) |∑_{n ≤ x, n ≡ a (d)} (liouville n : ℝ)|)
      ≤ C * x / (log x) ^ A
```
Mirror `HasLevel`'s exact shape (Salt/Maynard/Level.lean:28) with λ in
place of the prime indicator — the executor matches the house form
byte-compatibly (the max-over-residues via the same sup' pattern as
maxDiscrepancy). The wall is stated CONDITIONAL on `LambdaLevel (1/2)`
(the BV level the twin machinery uses).

**The rem-bound lemma**: under `LambdaLevel (1/2)`,
`rosserRemainder (sPlus x) D ≤ (the integer-count crumb ≈ D) + (the
λ-sum bound)` for `D ≤ √x/(log x)^B` — the integer part `|multSum −
x·(1/d)| ≤ 1 + |λ-AP-sum|` per d (⌊x/d⌋ vs x/d costs 1; the λ part is
the Prop's summand at a = 0... NOTE: the residue class is 0 mod d, which
is NOT reduced — the Prop must cover a = 0: state LambdaLevel with the
max over ALL residues a < d, not just reduced; flag for the gate).

## D4 — the wall (shape (c)) and its corollary (shape (b))

```
theorem parity_wall :   -- UNCONDITIONAL (post-amendment)
  ∀ᶠ x in atTop, ∀ (Φ : BoundingSieve → ℝ),
    (∀ s t, SieveAgree s t (D x) (Bbudget x) → |Φ s − Φ t| ≤ 2·Bbudget x) →  -- TOLERANT invariance (gate correction 3)
    (∀ s, Φ s ≤ s.siftedSum) →
    Φ (sMinus x) ≤ 2 + 2·Bbudget x                             -- ON sMinus (gate correction 2)
```
Reading: any tolerantly-invariant lower-bound certificate captures at
most 2 + 2B = o(the prime mass) from the prime-detecting instance —
NO invariant certificate captures a positive proportion of the primes.
The corollary (the vanishing-proportion punch, replacing the false
fixed-3 form):

```
theorem no_parity_beating_certificate :
  ¬ ∃ Φ (invariant-tolerant ∧ certificate),
      ∃ c > 0, ∀ᶠ x, c · siftedSum (sMinus x) ≤ Φ (sMinus x)
```

**The concrete core (the gate's recommended primary deliverable —
inhabited by construction, no abstract Φ):** the landed Rosser floor
`V(s) := totalMass·mainSum(μ⁻) − errSum(μ⁻)` satisfies
`V (sMinus x) ≤ 2 + Bbudget x` while `siftedSum (sMinus x) =
2(π(x) − π(√x))` — the undershoot → ∞. Land this FIRST (`rosser_floor_
undershoot`); the abstract wall generalizes it.

## D5 — the anti-vacuity obligations (Part III discipline)

1. The witness pair COMPILES as BoundingSieve values (weights_nonneg
   etc.) — instance construction is deliverable 1.
2. **The invariance class is inhabited** (GATE-ADJUDICATED): the
   tolerant form is the honest one — the landed lower-Möbius floor
   Φ_lower satisfies |Φ_lower s − Φ_lower t| ≤ 2B under SieveAgree
   (mainSum reads only shared fields; the errSums differ by ≤ 2B) and
   is a certificate. The exact form admits only trivial certificates
   (uninhabited by the real consumer — recorded). The concrete-core
   theorem needs no inhabitation argument at all.
3. Numeric sanity: at x = 10⁶, siftedSum₊ = 2 and siftedSum₋ =
   2(π(10⁶) − π(10³)) = 2·78330 — a compiled #eval-style check or a
   cited computation.

## D6 — the bridges (CRITICAL PATH post-amendment, not stretch)

Two nodes at the EFFECTIVE rate (gate correction 3's upgrade — the
qualitative o(y) does NOT suffice; the power-log rate does and is
reachable from the landed `siegelWalfisz_psiTot`):
(i) `Mmu_rate : |M_μ(y)| ≤ C·y/(log y)^A` from ψ (the effective
Tauberian bridge); (ii) `Mlambda_rate` via λ = μ∗1_squares (the
hyperbola fold preserves the rate — log(x/d²) ≥ log x/2-form on the
contributing range... derive honestly; the gate verified the budget
shape). These feed LambdaSummatory; THE WALL SHIPS UNCONDITIONAL.

## Nodes (post-gate)

Q6a-1 (defs + instances at the ≤ z fix + evaluations + the pointwise
rem identity) ∥ Q6a-3 (the two bridge nodes, D6) → Q6a-2 (the concrete
core rosser_floor_undershoot FIRST, then the tolerant wall + the
vanishing-proportion corollary + the Φ_lower inhabitation + numeric
sanity). THE GATE RAN (GO_W_CORRECTIONS, all applied above): three
tears caught pre-freeze — the ≤ z false lemma, the dead-hypothesis
flagship, the uninhabited/false corollary — plus the unconditionality
amendment. The gate report: the exploration ledger, 2026-07-15.
