# Q6b DESIGN — TwinB_min, the door (Fable freeze, PRE-GATE)

*2026-07-15, off the Q6b-recon (the exploration ledger ~18:35). One
executor node after the gate. The registered intent: the minimal
parity-breaking input for twins, precisely stated; the implication as
the stretch; the deep gap stated-not-attempted.*

## D1 — the two Props (the door) — POST-GATE (C1/C2/C4 applied)

File: `Salt/TwinBar/TwinDoor.lean`. House named-Prop convention.
Prerequisite named defs (GATE CORRECTION C1 — the carrier is
Λ-WEIGHTED, so the main term is one log up from the naive twin count,
and the window [x/2, x−2] halves the constant):

- `twinC2 : ℝ := ∏'_{p prime, p > 2} (1 − ((p:ℝ) − 1)⁻²)` — the
  GENUINE Euler product (GATE CORRECTION C2: the def must be backed
  by a `Multipliable` witness — mathlib's tprod junk-defaults to 1
  without it, which would satisfy positivity on a lie. The chain:
  summability of (p−1)⁻² on the prime subtype →
  `Real.multipliable_of_summable_log'` → tprod = exp(tsum log) > 0.
  Priced C-TIER; the executor lands it as its own section and may
  STOP-AND-FLAG on it alone if mathlib's Euler-product support
  resists — the Prop pair still lands with twinC2 as a def + the
  positivity as the flagged sub-node.)
- `twinMainTerm x := twinC2 * x / Real.log x` — the log-weighted,
  window-correct target (Σ_{n ∈ [x/2, x−2], n & n+2 prime} log n ~
  C₂·x/log x; 𝔖 = 2C₂ is the unweighted-count constant, NOT ours).

```lean
def TwinTypeII : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    |p1PrimeSum x 1 - twinMainTerm x|
      ≤ C * (x : ℝ) / (Real.log x) ^ A

def TwinB_min : Prop := TwinTypeII
```

GATE CORRECTION C4: θ was a dead variable in the sketched binder —
dropped. TwinB_min := TwinTypeII directly; the level-θ discussion
(what strength the bilinear consumption would need, > 1/2) lives in
the docstring as the literature-facing commentary, not a phantom
binder. The apDiscBilinCutoff reading likewise moves to the
docstring (the Q4 discipline) — the executor states the
correspondence in prose + a #check-able remark, not a second Prop.

## D2 — the implication (the stretch, IN scope)

`twinB_min_implies_twins : TwinB_min → TwinPrimeConjecture`
(Salt/Basic.lean:25's Prop), via:
1. (B) the main term dominates at A > 1 (post-C1: the error is
   x/(log x)^A against a main term of order x/log x):
   `p1PrimeSum x 1 ≥ (twinC2/2) * (x / Real.log x)` eventually —
   the Wall.lean:563ff rate-arithmetic pattern.
2. (B/C) positive p1PrimeSum mass ⟹ infinitely many twin survivors —
   the landed Assembly survivor endgame re-pointed from P₂ to P₁
   (`Set.infinite_of_forall_exists_gt`; the keep/window plumbing of
   TwinDeficit's p1PrimeSum carrier).

## D3 — THE DICHOTOMY (the headline; a corollary, not a new proof)

`wall_or_door` — GATE CORRECTION C3: carries the source theorem's
FULL hypothesis set explicitly: `(A : ℝ) (hA : 2 < A)
(hLS : LambdaSummatory A) (D : ℕ) (hD : 2 ≤ D)`. For any
Φ : BoundingSieve → ℝ with `∀ s, Φ s ≤ s.siftedSum` that captures a
positive proportion of `siftedSum (sMinus x)` eventually: Φ is NOT
SieveAgree-tolerant at level D — direct contraposition of the landed
`no_parity_beating_certificate` (Wall.lean:533; the gate verified the
quantifier match: same D, same 2B tolerance shape, same
eventually-form). Docstring states the partition + the λ ↦ −λ
involution mechanism.

## D4 — anti-vacuity (Part III discipline)

1. `twinC2_pos` via the genuine Multipliable witness (the
   zero-main-term alarm AND the C2 junk-default trap).
2. The upper half is landed (windowed_bilinear_BV_sqrtD) — cite in
   the docstring: TwinTypeII's error-control half is not vacuously
   false; the NEW content is strictly the main term.
3. The escape is inhabited: Chen's switchSieve reads at signed
   resolution (cite switchSieve_multSum_eq_apCount).
4. The landed carrier witnesses (p1_carrier_inhabited).
5. R4: TwinB_min is a DISTRIBUTIONAL premise (level-θ asymptotic
   with explicit saving), never a raw "p1PrimeSum is large" — the
   gate checks this reading.

## D5 — what is NOT attempted

Proving TwinB_min (the upper→asymptotic-lower upgrade = the P₁ lower
sieve; the large-sieve level-1/2 wall) is class D:
STATED-NOT-ATTEMPTED. It is the flagship's Challenge 2 and the
open-problems board's entry #2. TwinLambda (fixed-shift Chowla over
the landed Liouville carriers) and the Heath-Brown/Siegel dichotomy
are recorded as BOARD SIBLINGS in the module docstring — named, not
formalized (TwinLambda MAY be stated as a def if ≤ 10 lines, marked
open-on-both-sides).

## Gate mandate (adversarial, before the executor)

1. The R4/F≡1 reading of TwinTypeII: can the Prop be satisfied
   trivially (zero or negative main term; a degenerate
   twinSingularSeries carrier; an A-quantifier vacuity at small x)?
   Check the ∃C-per-A shape against the landed HasLevel/EHall
   conventions for the same trap the LambdaLevel design had (the
   a = 0 residue note).
2. The dichotomy's hypotheses: does wall_or_door as sketched
   actually follow from no_parity_beating_certificate's exact
   statement (read Wall.lean:533's quantifier structure — the
   fixed-level-D form; confirm the contraposition binds at the same
   D), or does it need the effective variant?
3. The D2 implication's step 2: confirm the survivor endgame
   re-point is genuinely B/C against the actual Assembly code (the
   keep/keepR plumbing at P₁), not a hidden C+ (the twin capstones
   are import-tangled per the G-IMPORT spine finding — the executor
   must import minimally).
4. twinSingularSeries: pick the formalization-cheapest positive
   carrier; check mathlib's tprod/Euler-product support suffices at
   B-tier.

Node: Q6b-DOOR (B/C + the C-tier twinC2 sub-obligation, ~300k,
one executor) — GATE RAN 2026-07-15: GO_W_CORRECTIONS, C1 (blocking:
the main term was one log off — the Λ-weighted carrier), C2 (the
tprod junk-default trap), C3 (hypothesis carry), C4 (dead θ). All
applied above. The D2/D4/import-hygiene checks passed clean; the
survivor re-point is confirmed EASIER than the P₂ endgame (keepR 1
already filters to primes — no prime-power crumb).
