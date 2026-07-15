# Q6b DESIGN — TwinB_min, the door (Fable freeze, PRE-GATE)

*2026-07-15, off the Q6b-recon (the exploration ledger ~18:35). One
executor node after the gate. The registered intent: the minimal
parity-breaking input for twins, precisely stated; the implication as
the stretch; the deep gap stated-not-attempted.*

## D1 — the two Props (the door)

File: `Salt/TwinBar/TwinDoor.lean`. House named-Prop convention
(EHall/HasLevel style). Prerequisite named defs:
`twinSingularSeries : ℝ := 2 * ∏' p-style` — USE the cleanest landed-
or-mathlib-expressible form (the executor picks the carrier — a tprod
over primes > 2 of (1 − (p−1)⁻²), or the equivalent convergent form —
and proves `twinSingularSeries_pos`, the F≡1-alarm obligation);
`mainTwinMass x := x / (log x)^2`.

```lean
def TwinTypeII (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    |p1PrimeSum x 1 - twinSingularSeries * mainTwinMass x|
      ≤ C * (x : ℝ) / (Real.log x) ^ A

def TwinB_min : Prop := ∃ θ : ℝ, 1/2 < θ ∧ TwinTypeII θ
```

θ enters through the level at which the bilinear form is consumed —
the executor states the literature-facing equivalent over
`apDiscBilinCutoff` (the Q4/WindowedBVStatement discipline: one Prop,
two readings) and records the correspondence in the docstring. If the
θ-slot resists a clean binding in the p1PrimeSum reading, the honest
fallback is TwinTypeII alone as TwinB_min (θ implicit in the error
saving) — report, don't force.

## D2 — the implication (the stretch, IN scope)

`twinB_min_implies_twins : TwinB_min → TwinPrimeConjecture`
(Salt/Basic.lean:25's Prop), via:
1. (B) the main term dominates at A > 2:
   `p1PrimeSum x 1 ≥ (twinSingularSeries/2) * mainTwinMass x`
   eventually — the Wall.lean:563ff rate-arithmetic pattern.
2. (B/C) positive p1PrimeSum mass ⟹ infinitely many twin survivors —
   the landed Assembly survivor endgame re-pointed from P₂ to P₁
   (`Set.infinite_of_forall_exists_gt`; the keep/window plumbing of
   TwinDeficit's p1PrimeSum carrier).

## D3 — THE DICHOTOMY (the headline; a corollary, not a new proof)

`wall_or_door` : every Φ : BoundingSieve → ℝ with `∀ s, Φ s ≤
s.siftedSum` (a lower-bound certificate) that captures a positive
proportion of `siftedSum (sMinus x)` eventually is NOT
SieveAgree-tolerant — direct from the landed
`no_parity_beating_certificate` (Wall.lean:533) by contraposition.
Docstring states the partition: tolerant ⟹ parity-blind (the wall);
parity-effective ⟹ signed-weights reader (the door). The λ ↦ −λ
involution note (the recon's hinge — the |rem| bounds are literally
identical on the witness pair) goes in the docstring as the
mechanism.

## D4 — anti-vacuity (Part III discipline)

1. `twinSingularSeries_pos` (the zero-main-term alarm).
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

Node: Q6b-DOOR (B/C, ~250k, one executor) after the gate.
