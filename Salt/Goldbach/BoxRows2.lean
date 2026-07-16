/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.D0Win
import Salt.Goldbach.PDiag
import Salt.Goldbach.Agg

/-!
# G-BOXROWS2 — the per-annulus box-price packagings (PARTIAL + the z-bound BLOCKER)

Design: the twin's `Salt/Chen/FinA3.lean` (`box_price_indep`) / `FinA3b.lean`
(`low_price_indep`/`sym_price_indep`) — the arg-free per-box price dischargers that fill the
`hprice`/`hpriceSym`/`hpriceLow` slots of `gold_hBVblocksW_discharge'` (PDiag) via a DEAD/LIVE
case split (DEAD → the carrier-vanish, LIVE → the D0-window engine).  This file assembles the
Goldbach mirror at the OUTER DYADIC ANNULUS axis.

## What lands here (sorry-free) vs. what is BLOCKED

* §1 **`gold_box_price_row_dead`** — the DEAD-branch per-box price row (UNCONDITIONAL): a box whose
  window start `2^i` sits at/above the carrier cap has an empty carrier, so both annulus-cutoff sums
  vanish and any nonneg `Price` discharges the `hprice` slot.  Direct reuse of
  `gold_box_price_vanish` (BoxRows §2).  Reusable named form of the BoxRows §4 example — the DEAD
  half of the case split, ready for the assembly.
* §2 the interface pins — `gold_hSum_at_op`'s conclusion is byte-for-byte the `hSum` slot of
  `gold_hBVblocksW_discharge'` (deliverable 3's landed half); the LIVE-branch obligation is pinned.

## THE z-BOUND BLOCKER (the LIVE branch — STOP-AND-FLAGGED; see docs/blueprints/flags.md)

The LIVE branch must invoke `gold_box_price_engine_at_live_annulus` (D0Win §3), whose hypothesis
`hz : (z : ℝ) ≤ (goldCut Ne (ka+1) : ℝ) ^ (1/8)` is the per-annulus z-bound feeding
`gold_kfloor_live_annulus`.  At the operating point `z := opZ N = ⌊N^{1/8}⌋` this hypothesis is
**FALSE for EVERY annulus**:

  `goldCut N (ka+1) ≤ N/2`, yet `(opZ N)^8 ≥ (N^{1/8}-1)^8 > N/2` for `N ≥ 2^40`,

so `(opZ N)^8 > goldCut N (ka+1)`, i.e. `opZ N > (goldCut N (ka+1))^{1/8}`.  The twin avoids this
because its boxes tile ONE global window `(x/2, x]` (`kfloor_of_live_box` uses `z ≤ x^{1/8}` at the
GLOBAL `x`, which `opZ x ≤ x^{1/8}` supplies).  The Goldbach annulus decomposition replaces the
single global scale by per-annulus scales `goldCut ≤ N/2`, while `z ≈ N^{1/8}` stays global — the
`z^8 > N/2 ≥ goldCut` mismatch is structural, and live boxes provably exist (boxes with
`2^{k'} > opY N / 2` in the boundary), so the DEAD branch does not cover them.  The honest live-box
floor is `goldCut N (ka+1) > z·(opY N)²/4`, which forces `z ≲ N^{2/21}` for the 7/16 floor to hold;
`opZ N = N^{1/8}` overshoots by `N^{5/168}`.  Resolution is design-tier (a smaller sifting level, or
a z-dependent D0-window floor) — recorded in `flags.md`, NOT fudged here.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. The DEAD-branch per-box price row (unconditional — the case split's DEAD half) -/

/-- **`gold_box_price_row_dead`.**  A DEAD box (`min (z·pieceN k' + 1) (N/2 + 1) ≤ 2^i`) has an
empty carrier, so the TWO-cutoff annulus box price (the exact `hprice`-slot LHS of
`gold_hBVblocksW_discharge'`, at `T₂ = goldCut N (k+1)`, `T₁ = goldCut N k`) is `0 ≤ P` for ANY
nonneg price `P`.  The reusable named form of the DEAD half of the box case split — direct reuse of
`gold_box_price_vanish`, `Dset`-generic. -/
theorem gold_box_price_row_dead {z y : ℕ} {ε₀ : ℝ} {j k' k i N Q a : ℕ} {P : ℝ}
    (hcap : min (z * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i) (hP : 0 ≤ P) (Dset : Finset ℕ) :
    (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
          (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
          (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
          (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
      + (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
            (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
            (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
            (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
      ≤ P := by
  rw [gold_box_price_vanish hcap Dset]; exact hP

/-! ## 2. Interface pins — the slots the packagings feed, and the LIVE-branch obligation

Two disciplined checks recording the exact downstream interface:

* the DEAD row above discharges `gold_hBVblocksW_discharge'`'s `hprice` slot against any nonneg
  price (the `hprice`-slot LHS is exactly `gold_box_price_row_dead`'s LHS at `Dset :=` the QImage);
* `gold_hSum_at_op`'s conclusion is byte-for-byte the `hSum` slot of
  `gold_hBVblocksW_discharge'` (compare `Agg.lean:93-101` with `PDiag.lean:552-559`) — deliverable
  3's landed half; the CONCRETE `Price`/`PsymK`/`PlowK` bounds (`hbox`/`hsym`/`hlow`,
  `Agg.lean:84-88`) it consumes are the LIVE per-box prices, hence blocked by the z-bound above. -/

section InterfacePins

/-- The DEAD box fills `gold_hBVblocksW_discharge'`'s `hprice` slot for ANY nonneg price. -/
example {z y : ℕ} {ε₀ : ℝ} {j k' k i N Q a : ℕ} {P : ℝ} {Dset : Finset ℕ}
    (hcap : min (z * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i) (hP : 0 ≤ P) :
    (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
          (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
          (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
          (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
      + (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
            (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
            (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
            (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
      ≤ P :=
  gold_box_price_row_dead hcap hP Dset

-- the aggregate whose `hSum` slot `gold_hSum_at_op` fills (byte-identical conclusion)
#check @Salt.Goldbach.gold_hSum_at_op
-- the terminal consumer whose `hprice`/`hSum` slots the packagings feed
#check @Salt.Goldbach.gold_hBVblocksW_discharge'
-- the vanish keystone the DEAD row reuses + the LIVE engine (its `hz` is the flagged blocker)
#check @Salt.Goldbach.gold_box_price_vanish
#check @Salt.Goldbach.gold_box_price_engine_at_live_annulus
#check @Salt.Goldbach.gold_kfloor_live_annulus

end InterfacePins

end Salt.Goldbach
