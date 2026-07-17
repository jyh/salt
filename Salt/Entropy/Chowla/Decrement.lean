/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The composition: the entropy-decrement headline (Chowla / Liouville, Lemma 3.1)

The wave-IV keystone of the A-R2 rung — the first information-theoretic argument
in formalized analytic number theory.  It fuses the two frozen outputs of the
spine into Tao 1509.05422 Lemma 3.1 (Liouville form):

* wave III's telescope `tower_telescope` (`Salt/Entropy/Chowla/Tower.lean`): IF
  the headline mutual-information bound fails (strictly) at every tower level
  `j < J`, the per-symbol entropy drops by the full `towerDropSum` from `H_0` to
  `H_J`; and
* wave IV's contradiction assembly `decrement_exists_of_tower`
  (`Salt/Entropy/Chowla/Endpoints.lean`): that telescoped drop, against the
  ceiling `e(H_0) ≤ log 2`, the floor `0 ≤ e(H_J)` and the barely-divergent
  `R.hJcon` (`log 2 < towerDropSum`), is impossible — so the bound holds at some
  `H_j ∈ [H₋, H₊]` with `a ∣ H_j`.

The only seam is polarity: `decrement_exists_of_tower` phrases the all-levels
failure as `∀ j < J, ¬ MIbound R H_j` (with the private, reducible `MIbound`
defeq to the explicit headline inequality), whereas `tower_telescope` consumes
the direct strict form `H_j/(log·logloglog) < towerMI R j`.  `not_le` converts
`¬ (I ≤ b)` to `b < I` per level; `towerMI`/`towerEntropy` unfold (defeq) to the
raw `I[…]` / `H[…]/…` spellings the two files use, so no rewriting is needed.

The anti-vacuity `∃ R : ChowlaRegime` (where `R.hJcon`'s barely-divergent series
actually lives) is a SEPARATE node — this file is `R`-parametric.
-/
import Salt.Entropy.Chowla.Tower
import Salt.Entropy.Chowla.Endpoints

open MeasureTheory ProbabilityTheory Real

namespace Salt.Entropy.Chowla

/-- **THE HEADLINE** (Tao 1509.05422 Lemma 3.1, Liouville form).  In the Chowla
regime there is an admissible window width `H ∈ [H₋, H₊]` with `a ∣ H` at which
the Liouville/residue mutual information is below the decrement threshold
`H / (log H · logloglog H)`.

Proof: `decrement_exists_of_tower` reduces the goal to the telescope `htele`
(the all-levels-failure ⇒ telescoped-drop implication) and the tower-range facts
`hmono`.  The telescope is `tower_telescope` with each level's failure hypothesis
`¬ MIbound R H_j` transported to the strict `H_j/(log·logloglog) < towerMI R j`
by `not_le.mp` (defeq unfolds the private reducible `MIbound` and the `towerMI`
definition).  The range facts are `chowlaTower_ge`/`chowlaTower_le_Hhi`. -/
theorem entropy_decrement (R : ChowlaRegime) :
    ∃ H : ℕ, R.Hlo ≤ H ∧ H ≤ R.Hhi ∧ R.a ∣ H ∧
      I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω]
        ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) :=
  decrement_exists_of_tower R
    (fun hfail => tower_telescope R (fun j hj => not_le.mp (hfail j hj)))
    (fun j hj => ⟨chowlaTower_ge R j, chowlaTower_le_Hhi R (le_of_lt hj)⟩)

end Salt.Entropy.Chowla
