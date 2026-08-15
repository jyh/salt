/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.SpineFinal

/-!
# The spine's ε-floor CONSUMPTION FENCE (wall-L2)

Design provenance: the 08/14 wall-dream lens `L2-sieve-weight`, candidate statement
`spine_eps_constant_floor`; the refuter's verdict calls it byte-CONFIRMED and "the
dream's best line".  This file lands it.

## What the fence is for

The log-Chowla-2 spine's terminals deliver ONE margin.  `log_chowla_two_budget_head`
(`SpineFinal.lean`) is an existential over a single `ε : ℚ`, chosen by
`exists_rat_btwn` strictly below the four-arm constant
`min (min (min (cE/(32·log 4)) (1/2)) (cD3/16)) (cD3/(16·C))`, and every downstream
terminal (`log_chowla_two_door_only_xi`, `log_chowla_two_door_only`, and the `MR`
mint `logChowla2_ineffective_v7`, whose `∃`-prefix carries the explicit floor
`1/500 ≤ ε`) inherits that single margin.  The margin is a CONSTANT: it is floored
away from `0` by constants of the construction, not driven to `0` by any parameter a
consumer controls.

Some slots need the opposite.  A sieve-density plug at unbounded `z` needs a saving
below the sifted density `W(z) ≍ (log z)^{-2} → 0`; a rate-form demand needs
`ε → 0`.  A constant-margin statement can never serve such a slot — its own
resolution is coarser than the demand from some point on.  That is not a defect of
the terminal; it is the shape of the object, and this file freezes the shape so that
no future wave spends a campaign discovering it.

## What is landed

* `margin_fails_vanishing_demand` — the reusable arrow: for ANY constant margin
  `ε > 0` and any demand `W` with `W z → 0`, eventually `¬ (ε ≤ W z)`.  This is the
  fence in the form a consumer meets it: hold a constant margin, and a vanishing
  demand is unmet from some scale on.
* `margin_not_forall_of_vanishing_demand` — the same, in the form a miswiring would
  need to be false: no constant margin `ε > 0` satisfies `ε ≤ W z` at every scale.
* `spine_eps_constant_floor` — the headline, at the landed terminal:
  `log_chowla_two_budget_head`'s conclusion VERBATIM, together with the fence at that
  terminal's own `ε`.  Reproducing the terminal in the statement makes this a
  tripwire: if the spine head's shape ever changed from a single-`ε` existential to
  an `∀ ε`-family, this statement would stop type-checking against it.

## Honesty block

Nothing here proves anything new about Chowla, about the door, or about twins.  It is
a consumption fence: an interface fact about a landed object's shape, kernel-checked
so it cannot be forgotten.  The blindness bound it encodes — a constant-`ε`
correlation statement fits the whole sifted set inside its own resolution — is the
parity wall restated from the spine side, not a work item and not a step toward one.
-/

open Filter Topology

namespace Salt.Entropy.Chowla

/-! ## The reusable arrow -/

/-- **A constant margin never meets a vanishing demand.**  If a consumer's required
saving `W z` tends to `0`, then for every fixed `ε > 0` the demand `ε ≤ W z` fails
from some scale on.  This is the general shape of the fence; the spine's terminals
supply the `ε` (see `spine_eps_constant_floor`). -/
theorem margin_fails_vanishing_demand (ε : ℚ) (hε : 0 < ε) (W : ℕ → ℝ)
    (hW : Tendsto W atTop (𝓝 0)) :
    ∀ᶠ z in atTop, ¬ ((ε : ℝ) ≤ W z) := by
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  filter_upwards [hW.eventually_lt_const hεR] with z hz
  exact not_le.mpr hz

/-- **The miswiring is impossible, not merely eventual.**  No constant margin
`ε > 0` satisfies a vanishing demand at every scale. -/
theorem margin_not_forall_of_vanishing_demand (ε : ℚ) (hε : 0 < ε) (W : ℕ → ℝ)
    (hW : Tendsto W atTop (𝓝 0)) :
    ¬ ∀ z : ℕ, (ε : ℝ) ≤ W z := by
  intro hall
  obtain ⟨z, hz⟩ := (margin_fails_vanishing_demand ε hε W hW).exists
  exact hz (hall z)

/-! ## The fence at the landed terminal -/

/-- **`spine_eps_constant_floor` — the spine head's margin is a CONSTANT, and no
vanishing demand can cite it.**

The first four components are `log_chowla_two_budget_head` verbatim: one `ε : ℚ`, one
door threshold `δ₀ > 0`, and for every extra regime-floor demand a regime `R` at that
same `ε` on which log-Chowla-2 does not fail, conditional only on the Ξ_H-restricted
door.  The last component is the fence: for any consumer demand `W` with `W z → 0` —
a sieve density at unbounded `z`, or any rate-form saving — the terminal's `ε` fails
the demand `ε ≤ W z` from some scale on.

So the spine head is unusable in any slot that needs the margin to vanish, and this
is a fact about the terminal's SHAPE (a single existential margin floored by
construction constants), not about the strength of its proof.  The same shape is
carried explicitly by the `MR` mint `logChowla2_ineffective_v7`, whose `∃`-prefix
delivers `1/500 ≤ ε`.

No claim about twins, about Chowla, or about the wall is made or implied here. -/
theorem spine_eps_constant_floor (W : ℕ → ℝ) (hW : Tendsto W atTop (𝓝 0)) :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      (∀ extraFloor : ℕ, ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
          ¬ logChowla2Fails R.eps R.x R.ω) ∧
      (∀ᶠ z in atTop, ¬ ((ε : ℝ) ≤ W z)) := by
  obtain ⟨ε, δ₀, hε, hδ₀, hbody⟩ := log_chowla_two_budget_head
  exact ⟨ε, δ₀, hε, hδ₀, hbody, margin_fails_vanishing_demand ε hε W hW⟩

end Salt.Entropy.Chowla
