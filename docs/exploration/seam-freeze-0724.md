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
