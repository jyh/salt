/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.SuperClose

/-!
# FPC — the switch-point `Fchain` certificate (catch #58a fix)

Design: `docs/blueprints/flags.md`, `2026-07-14 ★★ THE END-TO-END RE-GATE — catch #58`.

Catch #58a: the A₃ switch step was consuming the *uniform* `Fchain ≤ 268/100` (the
`[4/3,3]`-grid sup, `Fchain_A2_final`) at the switch abscissa `s ≈ 1.4997`, wasting the
decay of `1/s`.  The honest point value at the switch window is far smaller.  This node
evaluates the **landed identity** at the switch window `[1.49, 1.51]`.

## The identity, evaluated at a point

`MassLedger.Fchain_mass_ledger` gives, for `1 ≤ N` and `s ∈ [1,3]`,

  `Fchain N s = 1 + (3 − s)/s + (Σ_{K} massE k)/s`,   `K = {even k : 2 ≤ k < N}`,

and `SuperClose.massSum_le_A2_final` gives `Σ_{K} massE k ≤ 43/75` for **every** `N`
(the two index sets — `(Finset.range N).filter (fun k => Even k ∧ 2 ≤ k)` — are literally
identical, so they compose with no reindexing).  Writing `M := Σ_{K} massE k`, the ledger
**collapses**:

  `1 + (3 − s)/s + M/s = (3 + M)/s`

which is **strictly decreasing in `s`** (numerator `3 + M > 0`).  Hence on the switch window
`[149/100, 151/100]` the supremum is at the left endpoint `s = 149/100`, where with the
worst-case mass `M = 43/75`:

  `Fchain ≤ (3 + 43/75)/(149/100) = (268/75)·(100/149) = 26800/11175 = 1072/447 ≈ 2.39821`.

## The frozen constant

Worst-point value: **`1072/447 ≈ 2.39821`** (exact rational — the ledger is an identity and
`43/75` is exact).  Candidate targets: `24/10 = 2.40` holds but with only `0.075%` slack (it
would *break* under any re-gate loosening the mass bound past `44/75`); `243/100 = 2.43` gives
`1.33%` slack.  Per the design's "tightest clean rational ≥ worst point with ≥ 1% slack" rule,
we freeze **`243/100 = 2.43`** — luxuriously below the razor's `2.6403` ceiling (indeed below
the `2.5` "luxurious" line), and robust to a modest re-gate of the mass budget.

## Output

* `Fchain_switch_le` : `Fchain N s ≤ 243/100` on the switch window `[149/100, 151/100]`,
  for every truncation depth `N ≥ 1`.  Stated in `Set.Icc`-form so the H-glue's
  window-membership lemma (`logRatio y Dlev ∈ [1.49, 1.51]` — not this node) plugs directly.
-/

open MeasureTheory intervalIntegral Set

namespace Salt.Chen

/-- **The switch-point `Fchain` certificate** (catch #58a).  On the switch window
`s ∈ [149/100, 151/100] ⊂ [1,3]`, `Fchain N s ≤ 243/100` for every depth `N ≥ 1`.

Proof: the mass ledger (`Fchain_mass_ledger`) collapses `Fchain N s` to `(3 + M)/s` with
`M := Σ_{even k, 2≤k<N} massE k ≤ 43/75` (`massSum_le_A2_final`).  Being decreasing in `s`,
its window supremum is at `s = 149/100`, value `1072/447 ≈ 2.398 < 243/100`. -/
theorem Fchain_switch_le (N : ℕ) (hN : 1 ≤ N) :
    ∀ s ∈ Set.Icc (149 / 100 : ℝ) (151 / 100), Fchain N s ≤ 243 / 100 := by
  intro s hs
  obtain ⟨hs149, hs151⟩ := hs
  have hs1 : (1 : ℝ) ≤ s := by linarith
  have hs3 : s ≤ 3 := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have hsne : s ≠ 0 := hs0.ne'
  rw [Fchain_mass_ledger N hN hs1 hs3]
  have hMle : (∑ k ∈ (Finset.range N).filter (fun k => Even k ∧ 2 ≤ k), massE k) ≤ 43 / 75 :=
    massSum_le_A2_final N
  set M := ∑ k ∈ (Finset.range N).filter (fun k => Even k ∧ 2 ≤ k), massE k with hMdef
  -- the ledger collapses to `(3 + M)/s`, decreasing in `s`
  have hcombine : 1 + (3 - s) / s + M / s = (3 + M) / s := by field_simp; ring
  rw [hcombine, div_le_iff₀ hs0]
  -- worst point: `3 + M ≤ 268/75` and `243/100·s ≥ 243/100·149/100 = 36207/10000 > 268/75`
  linarith

end Salt.Chen
