/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.Params
import Salt.Twelve.Certificate
import Salt.Twelve.MomentAtom
import Salt.Twelve.PhiUpper
import Salt.Twelve.MarkedPrime
import Salt.Twelve.BudgetPoly
import Salt.Twelve.BudgetMoment
import Salt.Twelve.W3Prep
import Salt.Twelve.MvMoment
import Salt.Twelve.BudgetMomentG
import Salt.Twelve.MvMomentG
import Salt.Twelve.MvI
import Salt.Twelve.MvJ
import Salt.Twelve.PhiUpperReindex
import Salt.Twelve.RelEngines
import Salt.Twelve.FstarNorm
import Salt.Twelve.MvSplit
import Salt.Twelve.QdiagBridge
import Salt.Twelve.PrimorialRatio
import Salt.Twelve.Pigeonhole12
import Salt.Twelve.CollisionYF
import Salt.Twelve.CollisionYF_S2
import Salt.Twelve.YsideCM
import Salt.Twelve.InnerS1
import Salt.Twelve.InnerS2
import Salt.Twelve.WinCore
import Salt.Twelve.WinFrontierDischarge
import Salt.Twelve.GapsFinal
import Salt.Twelve.JcalPos
import Salt.Twelve.FrontierM
import Salt.Twelve.QdiagFloor
import Salt.Twelve.GapsUncond
import Salt.Twelve.GapsOfLevel
import Salt.Twelve.WindowPNTDischarge
import Salt.Tactic.AuditAxioms

/-!
# Rung 4a (`explicit12`) — aggregate import

Explicit bounded gaps `≤ 12` from `WindowPNT` + `EHall`, via Maynard's `k = 5`
polynomial sieve. Design: `docs/blueprints/explicit12-design.md`.

Wave 1 (landed): `Certificate` (`M5_cert : M₅ > 2` in exact ℚ), `Params`
(`WindowPNT`/`EHall`, `hSeq 5 = {7,11,13,17,19}`, `diam ≤ 12`, spine audit),
`MomentAtom` (the one-dim moment atom, conditional on the narrow `PhiUpperAtom`).

Wave 2 (landed): `BudgetMoment` (`beta_sum` + `budget_moment`, the normalized
budget-factor moment via Crux 3), `MarkedPrime` (`marked_prime_phi`, the
single-prime marked-sum engine), `BudgetPoly` (the symbolic ℚ layer + ties to
`Certificate`), and `PhiUpper`'s analytic core (`powerful_sum_bounded`;
`phiUpperAtom_holds` discharges `PhiUpperAtom` modulo the `hReindex` residual).

Wave 3 (landed): `W3Prep` (`marked_sqf_phi` composite marked atom, `eval_mul/sq`,
`log_natCap_slip`), `MvMoment` (`decBox` + `mv_monomial`, the general-`n` moment
workhorse), `BudgetMomentG` (`marked_sqf_g` + `budget_moment_g`, the g-sandwich —
drained the `budget_moment_g` FABLE-QUEUE item), `MvMomentG` (`mv_monomial_g`, the
g-weighted workhorse), and the two keystones **`MvI`** (`mv_I` : the 5-dim first
moment `X⁵·simplexInt (sq (ofPoly F))`) and **`MvJ`** (`inner_contract` + `mv_J` :
the 4+2-dim second moment `X⁶·simplexInt (sq (contractAt m F))`). At `F★` these
conclude, via the `BudgetPoly` ties, `X⁵·Ical F★` and `X⁶·Σ_m Jcal m F★`.

Wave 4 (landed): the bridges from the moments to the `(D,W')`-generalized sieve
spine. `PhiUpperReindex` (**`phiUpperAtom_final : ∀ B≠0, PhiUpperAtom B`**,
UNCONDITIONAL — the `PhiUpperAtom` hypothesis is discharged everywhere);
`RelEngines` (constant-free relative marked/gap bounds vs `phiAtomSum`);
`FstarNorm` (`Fstar1` normalized weight `|yF|≤1`, `M5_cert1`, `primorial_hDlt`);
`MvSplit` (`mv_I_split`/`mv_J_split`/`inner_contract_rel` — the split-error
forms with `1/D` errors relativized to `phiAtomSum`, `∃A` before `W'`);
`Lemma53W` (`Salt/Maynard/`, free-`(W',D)` `lemma53_tightW`); and **`QdiagBridge`**
(`qdiag_bridge` : `Qdiag_mW 5 R W' m (yF F) ≈ X⁶·simplexInt (sq (contractAt m F))`).
Design corrections this wave (Opus, endgame-verified): the `mv_J_split`/
`qdiag_bridge` `1/D` buckets are MIXED-power `(1+X+PAS)⁶`, and `qdiag_bridge`
carries a second `κ⁻²·Y⁶/D²` term (both endgame-safe via `κ⁻¹ ≤ 5√D`).

Wave 5 + endgame (landed): `PrimorialRatio` (`primorial_ratio_le : κ⁻¹ ≤ 5√D`),
`Pigeonhole12` (`bounded_gaps_reduces_twelve`, the faithful pigeonhole
reduction), `WinCore` (the endgame capstone `gaps_le_twelve_of_inner` +
`win_ratio_core` + `WinFrontier` at `Dstar`), and `WinFrontierDischarge`
(`winFrontier_of`: frontier conjuncts 1–6 + threshold assembly).

Node B (route superseded by Node C; scaffolding landed): `CollisionYF` (NB-1 S1
reductions — exposed the crude-domination mirage), `YsideCM` (NB-2 — its `hD0`
is W'-opaque, documented unusable at primorial moduli), `CollisionYF_S2` (NB-3,
free-`(W',D)` S2 collision infrastructure).

Node C — THE CLOSURE (landed): `InnerS1` (NC-1, **`collision_yF_M`** — the
UNCONDITIONAL S1 collision atom, termwise + contamination partition), `InnerS2`
(NC-2, **`s2_inner_yF`** — the S2 atom with the g-weighted `(p−2)⁻²` prefactor,
mod the `hQd` qdiag comparison), `GapsFinal` (NC-3, `gaps_le_twelve_of_frontierM` at
the abstract Archimedean `primorial Dfin`, conditional on the frontier).

THE RUNG IS CLOSED (R1a/R1b/R2a/R2b/R2c, 2026-07-11): `JcalPos` (per-m
certificate positivity), `QdiagFloor` (the pointwise S₂ collision closure,
`∃Dthr` from `qdiag_bridge`'s `A`), `FrontierM` (`WinFrontierMW (D)` +
`winFrontierMW_of`: frontier conjuncts 1–6 at any `D ≥ 300`), and
`GapsUncond` — **`gaps_le_twelve (hPNT : WindowPNT) (hEH : EHall)`**, the
frozen target, UNCONDITIONAL beyond its two named analytic inputs, with the
Archimedes cutoff chosen existentially after the F-only constants.

WindowPNT seam (landed): `WindowPNTDischarge` — **`PiAsymp`** (ordinary PNT as
`π ∼ x/log x`, the `pi_alt'`-shaped interface) discharges the long-window
hypothesis via `windowPNT_of_piAsymp`, collapsing the two standing analytic
inputs of the capstone to `PiAsymp` + `EHall` in
`gaps_le_twelve_of_piAsymp` (a definitional composition, no new analytic content).
-/

/-! ## ⭐ THE TRACK'S AXIOM GATE (added 2026-08-26, math)

⛔ **WHY THIS BLOCK EXISTS: UNTIL TODAY THIS AGGREGATE AUDITED NOTHING — ON A CLOSED RUNG.**  A
census run for the helm's carried-debt order (`seat/briefs/2026-08-26-math-REPORT-uncovered-set.md`)
found `Salt/Twelve/All.lean` and `Salt/LS/All.lean` were **the only two track aggregates in the repo
with no `#audit_axioms` block** — every other `*/All.lean` carries one.  Measured audit-name
coverage of this track was **5 of 398 declarations (1%)**, the lowest in the repo, on a rung whose
own header says **THE RUNG IS CLOSED**.

⇒ 🔑 ***"CLOSED" IS A CLAIM ABOUT PROOFS; "AUDITED" IS A CLAIM ABOUT AXIOMS, AND A GREEN `lake
build` IS NEITHER.*** A rung can be closed, green, and completely ungated at the same time — which
is the shape of *a dead branch reading as coverage*.

Listed below are the rung's TERMINALS, the names its own header calls out — not all 398
declarations.  A deliberate first cut, honest about its scope: **this gate covers the named
results; helper lemmas are covered only through them.**  Widening it is cheap and welcome. -/
open Salt.Tactic in
#audit_axioms Salt.Twelve.M5_cert
  Salt.Twelve.phiUpperAtom_final
  Salt.Twelve.mv_I
  Salt.Twelve.mv_J
  Salt.Twelve.qdiag_bridge
  Salt.Twelve.primorial_ratio_le
  Salt.Twelve.bounded_gaps_reduces_twelve
  Salt.Twelve.collision_yF_M
  Salt.Twelve.s2_inner_yF
  Salt.Twelve.winFrontierMW_of
  Salt.Twelve.gaps_le_twelve_of_frontierM
  Salt.Twelve.gaps_le_twelve
  Salt.Twelve.windowPNT_of_piAsymp
  Salt.Twelve.gaps_le_twelve_of_piAsymp
