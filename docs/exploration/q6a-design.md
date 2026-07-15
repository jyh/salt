# Q6a DESIGN — the parity wall as an interface theorem (Fable freeze, pre-gate)

*2026-07-15. From the Q6a-recon (the pilot ledger): the honest shape is
the consumer-relative form (c) with the ε-agreement core (b); the
exact-agreement shapes are vacuous. This design freezes the statements
for the gate. The corpus convention (EHall/PiAsymp-style named Props)
carries the analytic input; the unconditional Σλ discharge is a stretch
sub-node.*

## D1 — the sifting instances (the Selberg witness pair)

Over `support = Icc 1 x` (as the sieve's ℕ-support), `prodPrimes = P(z) =
∏_{p < z} p` at `z = Nat.sqrt x`, shared density `ν(d) = 1/d`
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

## D3 — the analytic input (the named Prop, corpus convention)

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
theorem parity_wall (hλ : LambdaLevel (1/2)) :
  ∀ᶠ x in atTop, ∀ (Φ : BoundingSieve → ℝ),
    (∀ s t, SieveAgree s t (D x) (Bbudget x) → Φ s = Φ t) →   -- invariance
    (∀ s, Φ s ≤ s.siftedSum) →                                 -- a lower-bound certificate
    Φ (sPlus x) ≤ 2                                            -- ≤ the plus-instance's sifted sum
```
with the reading: any Agree-invariant lower-bound certificate is capped
at 2 — while the prime-detecting instance sMinus has sifted mass
2·π(√x, x] → ∞. Proof skeleton: invariance + the pair's SieveAgree
(D1 + D3's rem bounds) give Φ(sMinus) = Φ(sPlus) ≤ siftedSum(sPlus) = 2.
The ¬∃ corollary in the house genre:

```
theorem no_parity_beating_certificate (hλ : LambdaLevel (1/2)) :
  ¬ ∃ Φ, (invariant ∧ certificate ∧ ∀ᶠ x, 3 ≤ Φ (sMinus x))
```
(any invariant certificate claiming ≥ 3 primes-mass from the minus
instance is refuted — the constant 2 is the wall).

## D5 — the anti-vacuity obligations (Part III discipline)

1. The witness pair COMPILES as BoundingSieve values (weights_nonneg
   etc.) — instance construction is deliverable 1.
2. **The invariance hypothesis is inhabited by the REAL landed
   consumer**: exhibit `Φ_lower s := s.totalMass · mainSum(μ⁻) −
   errSum(μ⁻)`-style (the lower-Möbius floor at a fixed μ⁻ built from
   {prodPrimes, nu}) as (i) Agree-invariant given the budget (mainSum
   reads only the shared fields; errSum ≤ B on both sides — note the
   floor uses −errSum so invariance is within 2B: adjust the wall to
   `|Φ s − Φ t| ≤ 2B`-tolerant form OR make Φ_lower's errSum-free
   version the instance; THE GATE DECIDES which form is honest) and
   (ii) a certificate (the landed lower bound). Without this the wall
   delimits an empty consumer class.
3. Numeric sanity: at x = 10⁶, siftedSum₊ = 2 and siftedSum₋ =
   2(π(10⁶) − π(10³)) = 2·78330 — a compiled #eval-style check or a
   cited computation.

## D6 — the stretch (unconditional Σλ)

Two nodes, elementary route (the recon's costing): (i) M(y) = o(y) from
psiTot_pnt (the ψ↔M Tauberian bridge — the classical "equivalent forms"
argument, explicit constants); (ii) Σ_{n≤x} λ(n) = o(x) via λ = μ ∗
1_squares (the hyperbola fold). This discharges only the a = 0,
d = 1-ish part — the FULL LambdaLevel(1/2) is the λ-BV (C/D-tier, NOT
in the sprint). The wall therefore ships conditional; the stretch makes
the d = 1 instance unconditional as a corollary demonstration.

## Nodes

Q6a-1 (defs + instances + evaluations + the rem-bound lemma);
Q6a-2 (the wall + the corollary + the Φ_lower inhabitation + the
numeric sanity). Stretch Q6a-3 (D6). GATE FIRST (one adversarial lens):
the Agree definition's strength (too strong = vacuous wall, too weak =
false wall), the a = 0 residue flag in D3, the ±2B invariance-tolerance
choice in D5.2, and the honest-consumer inhabitation.
