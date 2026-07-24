# THE EQ-(24) SEAM FREEZE — the ball re-pin + the annulus split
## (Maestro design block, 2026-07-24 night. THE RE-PIN: JYH-RATIFIED
## 2026-07-24 ~21:20 — "Let's do the re-pin now and keep working.")

*Inputs: seam-scope-0724.md (the §8.3 mechanism + the object finding +
SHAPE 0/A/B), chi-check-0724.md, door-road-0724.md + corrections, T-RESHAPE's
ceiling note (AnnHead:424-490), the flags entry on the hsplit mismatch.
Status: FROZEN pending the refuter pass (R1/R2 firing now); the wave fires
on FIRE / REPAIR-THEN-FIRE.*

## THE RE-PIN (ratified)

The T1 head object moves from `annHead` (the full seam L-series at 1+σ —
Θ(T)-sized, the wrong family) to **the BALL LEG of the annulus mean square
of the dyadic seam polynomial**, bounded by measure × sup with the sup
supplied by PARTIAL SUMMATION from the landed `halasz_ball_decay`-grade
X-scaled sum bound (the MRT A.6→A.7 route). The head leg becomes **T-free**;
the (logX)² dies with the L-series. `annHead` + its rows + the polyT chain
stay landed as heritage/shelf (nothing edited, nothing deleted); the
`_of_floor` variants remain do-not-wire.

## The target (restated on the annulus — matching lemma14_contour's datum)

Fix the seam datum a := the dyadic coefficients of spoly at the seamCoeff
convention (the S2′/moment objects), T₀ := (logX)^{1/15}, the ball radius
r := (logX)^{1/16}, t₁ := a near-minimizer of M_range's window infimum
(∃ t₁ in the window with pretDistSq(datum, costwist t₁) ≤ M_range + 1).
Ann(T₀,T) := {t : T₀ ≤ |t| ∧ |t| ≤ T}. THE SEAM:

  ∫_{Ann} ‖spoly N a t‖² dt
    ≤ [BALL: ∫_{Ann ∩ {|t−t₁| ≤ r}}]  +  [FAR: Σⱼ ∫_{Ann ∩ 𝒯ⱼ}]  +  [𝒰: ∫_{Ann ∩ 𝒰 \ ball}]

- BALL ≤ 2r · sup² ≤ 2(logX)^{1/16} · 9·(e^{−cM} + (logX)^{−1/2+ε})²  [Z2+Z3]
  — MRT's own second-term grade; T-FREE.
- FAR (𝒯ⱼ) ≤ the landed moment rows (monotonicity into [−T,T]; the E1+Ej
  masses, T-general)  [Z5, cheap]
- 𝒰: the ONE remaining named binder hU after this wave — its supply is the
  §8.3 interior (L3-dyadic + L9-hZ + L12-herr ≈ 1–2k C, the NEXT block; the
  balance θ = ρ/3 at our ρ = 1/(32e) gives the honest exponent ≈ 0.0038 —
  c₀-existential posture, never literal 1/48).

## The stones (serial where dependent; new file Salt/MR/SeamSplit.lean except
## noted; ALL ADDITIVE — no landed line edited)

- **Z0** [A, ~60 total] `prop_A3_T1_row_annular_le` / `_moment_le`
  (AnnHead/Prop1Assembly appends): the ≤-weakened hsplit variants (a genuine
  eq-(24) yields inequalities; the = rows stay as heritage). Docstring points
  at the flags entry.
- **Z1** [B, ~150] `annulus_ball_far_split`: the 2-set setIntegral split of
  Ann into the (closed ∩) ball piece and the complement; measurability
  trivial (closed/open sets); integrability from spoly continuity (landed
  continuous_spoly precedent).
- **Z2** [C, 300–500] **THE BRIDGE** `spoly_sup_of_ball_decay`: partial
  summation (Abel over the Finset) — spoly N a t = A_t(2X)/(2X) − A_t(X)/X +
  ∫_X^{2X} A_t(u)/u² du with A_t(u) := Σ_{n≤u} aₙ n^{−it} (the twist inside
  A_t via the seamCoeff n^{−it₀}) ⇒ ‖spoly‖ ≤ 3·sup_{X≤u≤2X}‖A_t(u)‖/u.
  THE WORST CORNER (fail-fast): the ball-decay supply is at scale X only —
  the sup-over-u needs either (i) the hatKernel window re-instantiated at
  each u (check HalaszSeam's hatK support argument: the S1′ chain's X is a
  free parameter — expected YES), or (ii) a named uniformity binder hUnif
  carried honestly. If (i) fails AND (ii) would be vacuous, STOP — maestro
  re-rules.
- **Z3** [B, ~120] `ball_leg_grade`: measure×sup² composition; the exit in
  the e^{−2cM}·(logX)^{1/16} + (logX)^{1/16−1+2ε} form (state both summands;
  the c from B4's re-freeze c = 1/e as landed in the ball-decay chain).
- **Z4** [B, ~400] the partition machinery (SHAPE B, Decomp appends or
  SeamSplit): primeBlockPoly continuity [A]; BlockSmallAt sets closed
  (countable ∩ closed) [B]; Uset open/Tset Borel [A/B]; the
  integral_finset_biUnion disjoint additivity over Ann ∩ (⋃𝒯ⱼ ∪ 𝒰) [B];
  the annulus-restricted exhaustiveness from the landed
  exists_Tset_or_mem_Uset [A/B]. NOTE: Tset's single-δ shape vs MR's
  v-dependent e^{−αv/H} is DEFERRED to the §8.3 block (the 𝒰-leg is a named
  binder this wave; no Tset statement change now).
- **Z5** [A/B, ~100] `far_moment_leg`: ∫_{Ann∩𝒯ⱼ} ≤ ∫_{−T}^{T} (nonneg
  monotonicity) fed by the landed moment rows at the shifted coefficients.
- **Z6** [B/C, ~200] **the seam row** `prop_A3_T1_row_split`: the assembled
  honest inequality — Itot_Ann ≤ ballGrade + Gmom_crude + hU — with ball
  and moment CONCRETE and hU the one named binder (docstring: the §8.3
  supply map). This DISCHARGES hsplit as an inequality; the T-gate is GONE
  (ball T-free, moment T-general, hU's supply is where all remaining
  T-structure lives).

## Corner ledger

- The t₁ existence: M_range is an sInf over a nonempty window (the window
  is nonempty for X past the threshold — check DistHalasz's window
  conventions; state ∃ t₁ with dist² ≤ M_range + 1 via Real.sInf
  approximation [A/B]). The ball may protrude past the annulus — Z1 uses
  Ann ∩ ball, protrusion only shrinks.
- The X-power page (BRIDGE-CHECK's three-X ghost, now resolved): the
  X-scaled U divides by u ∈ [X,2X] — factor-2 constants only; NO X² object
  anywhere; state the page in Z2's notes before Lean.
- The ball-decay input: `halasz_ball_decay`'s exact binder (frozen interface
  per the s8 contract) — Z2 CONSUMES it, never restates it.
- The far leg's T: the moment masses carry (2T+20N) — the consumer's
  T = X/h₁ lands Gmom ≍ X/h₁-grade; that is the honest §8-row size (MR's
  own E-terms are mass-grade); the DECAY of the T1 row lives in the ball
  leg + hU alone. No row claims decay it does not have.
- No literal 1/48, 1/50, 1/16-as-ρ anywhere in statements — the exponents
  are ∃-quantified or named constants (Benli discipline).

## Refuter charges (R1/R2, firing now)

1. **BRIDGE-REF**: attack Z2 — derive the Abel identity yourself over a
   Finset with the twist placement; the sup-over-u uniformity corner against
   HalaszSeam's ACTUAL S1′ chain (is X free? name the exact lemma/binder
   that would need re-instantiation); the X-power page at the four corners
   (u = X, 2X; the 1/u² integral's constants); whether the ball-decay
   binder's shape (the frozen halasz_ball_decay) actually delivers
   sup-compatible data or only the single-scale bound.
2. **GEOM-REF**: attack Z1/Z4/Z6 — the t₁ near-minimizer existence and the
   ball/annulus geometry (boundary/multiple minimizers; the window's own
   |t| ≤ X cap vs the ball); the partition's measurability chain against
   Decomp's ACTUAL defs (BlockSmallAt's quantifier structure — countable?);
   the Z6 row's binder shapes vs the landed moment rows BYTE-level; the
   grade page of Z3 (measure×sup² arithmetic; the e^{−2cM} vs e^{−cM}
   bookkeeping — the ball-decay U is already the SUM bound, squaring is
   Z3's job — check no double-squaring).

Wave fires on FIRE / REPAIR-THEN-FIRE with repairs applied.

## ⟦AMENDMENT V2 — the refuter ruling (maestro, 2026-07-24 ~23:00)⟧

Verdicts: BRIDGE-REF **HOLD** (R-3 CONFIRMED-FATAL; R-1/R-2 repairable;
R-4 unfounded — the X-power page clean); GEOM-REF **REPAIR-THEN-FIRE**
(all four repairable, rich repairs). RULING: the freeze's headline supply
claim was WRONG — `halasz_ball_decay` is a scalar re-arrangement (U/Uhead/
Utail free reals), NOT a landed sum bound; the pointwise ball sup's only
mapped supply is the open frontier (hpret/hbridge/hgrade — HExit's own
CODA), and pointwise E is main-term-sized in the intended regime. The catch
is MINE (the maestro conflated the socket with a supply — the same error
class as the annHead object finding, caught by the refuters before one
executor token burned). THE WAVE FIRES AT REDUCED, TRUE SCOPE:

- **Z0** unchanged.
- **Z1** + hypotheses `hT₀ : (logX)^{1/15} ≤ T`, `hTX : T ≤ X`, `0 ≤ T`
  (window nonemptiness is a T-condition, NOT an X-threshold; Ann ⊆ window
  needs T ≤ X — MR Step 0 licenses it; the consumer has T = X/h₁ ≤ X).
- **Z2a** [B] the UNCONDITIONAL Abel inequality: hypotheses hsupp
  (∀ n ≤ X, a n = 0) + the convention-proof form spoly = A_t(N)/N +
  ∫_1^N A_t(u)/u² du (Abel from 1; NO −A(X)/X identity — the closed-at-X
  trap), exit ‖spoly‖ ≤ (1+log 2)·S ≤ 3S. No ball-decay input.
- **Z2b** the pointwise ball sup becomes the NAMED BINDER
  `hSup : ∀ t, |t−t₁| ≤ r → ∀ u ∈ [X,2X], ‖A_t(u)‖ ≤ S·u` with the unmet
  supply documented in-docstring (the T1 frontier; GRAND-COMP's pointwise
  wall; the M-form discipline: any M in the exit is stated in FLOOR form
  per scale — never M_range at X for a bound obtained at u).
- **Z3** consumes hSup (measure×sup²; the squaring bookkeeping per
  GEOM-REF R-4's check).
- **Z4** repairs: `MeasureTheory.integral_biUnion_finset` (the correct
  name); Uset-open via the explicit Finset.Icc 1 J restriction (or plain
  measurability — all the split needs); Tset case-split on 1 ≤ j ≤ J;
  IntegrableOn via `Measure.integrableOn_of_bounded` (bounded+measurable,
  NOT compactness).
- **Z5** THE J-FACTOR TRAP KILLED: collapse the far leg via the biUnion
  identity FIRST (one integral over the union), THEN one monotonicity into
  [−T,T] — never Σⱼ of J separate copies (J grows with X; catch #253).
- **Z6** is a NEW statement (the landed _row_ lemmas are NOT consumable —
  their hsplit demands annHead): TWO data parameters (the dyadic
  `a : ℕ → ℂ` with hsupp + ‖a‖ ≤ 1 for the spoly slot; the multiplicative
  seam datum `fseam := seamCoeff (ellLin g) 1 t₀` for the M_range slot —
  the DATUM CONFLATION was fatal as drafted: dyadic a has a_p = 0 at p ≤ X,
  degenerating pretDistSq); Re = 1 throughout (NO n^{−σ} rescale — that was
  the B-pin's line, now retired with annHead); the intervalIntegral ↔
  setIntegral bridge stated (integral_of_le + null endpoints). Exit: the
  PROVEN partition inequality Itot_Ann ≤ ball(hSup-bounded) + far(one
  MVT-monotonicity bound stated honestly as the crude placeholder) with
  the named binders hSup + hU (the §8 interior sharpening of the far leg).
- t₁: obtain via `Real.lt_sInf_add_pos` (Nonempty only — no BddBelow);
  spend NO stone on minimizer properties (the grade is range-uniform).

THE NEXT DESIGN TARGET (not this wave): hSup's supply — the pointwise
ball Halász bound. Its honest map: the corpus's T1 frontier (hpret via
SupF's B-ladder + hbridge + hgrade), now with the L-series machinery
landed; alternatively the L² route only (drop pointwise, take the ball
leg in mean-square via a Vtail-style tent argument at the ball scale —
scope BOTH in the morning block).
