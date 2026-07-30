/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Exit

/-!
# ⟦S0-TOWER⟧ — the split socket at the `K = 9/2` tower law

`M4Exit.m4_exit_socket_split` forwards the head's tower endpoint law

  `50 ≤ loglog R.Hlo → loglog R.Hhi ≤ (loglog R.Hlo)^5`

(⟦THE NAMED AMENDMENT⟧, the 2026-07-29 anchor ruling).  S11-SCOPE's two-λ audit
(2026-07-30) showed that exponent is TOO LOSSY for the compose: the P2 arm reads
`λ₊ = loglog R.Hhi`, the drift arm caps `λ₋ = loglog R.Hlo`, the tower is their
only bridge, and at `K = 5` the two demands are `b ≥ 46.0` against `b ≤ 31.3` —
the window is EMPTY by 1.47×.  The compose needs `K ≤ 4.9`.

Ruling C-A (GRANTED 2026-07-30) is that `K = 9/2` is FREE ARITHMETIC: the landed
proof's own crossing budget is `w_J − w₀ ≤ (40/19)·log 2 + 7/300 = 1.4826`, and
`log (9/2) = 1.50408` clears it exactly as `log 5 = 1.6094` does — the landed
proof spends the budget against the line `3/2`, and `3/2 < log (9/2)` too
(`exp(3/2) = 4.4817 < 4.5`).  The twin chain is

  `TowerExport.tower_loglog_le_45`
    → `TowerExport.chowlaRegime_exists_param_tower_45`
    → `TowerExport.chowlaRegime_exists_param_head_tower45'`
    → `SpineFinal.log_chowla_two_budget_head_g_45`
    → `m4_exit_socket_split_45`  (this file — the MR-side handoff).

Every stone is ADDITIVE; the `K = 5` chain is untouched and both live side by
side.  `TowerExport.rpow_nine_halves_le_pow_five` weakens the `9/2` payload back
to the landed `^5` shape under the socket's own guard (`50 ≤ loglog R.Hlo`, so
the base is `≥ 50 ≥ 1`), which is the one-way direction: any consumer wired to
`^5` reads this socket for free; a consumer that needs `9/2` must take the twin.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **THE SPLIT SOCKET AT `K = 9/2`** (`m4_exit_socket_split_45`) — the additive
twin of `M4Exit.m4_exit_socket_split` whose forwarded tower conjunct is

```
50 ≤ loglog R.Hlo → loglog R.Hhi ≤ (loglog R.Hlo)^(9/2)
```

(`SpineFinal.log_chowla_two_budget_head_g_45`, ultimately
`TowerExport.tower_loglog_le_45` at the minimal crossing length `towerJmin`).

Statement diff against the landed socket: the exponent alone — `rpow (9/2)` in
place of `npow 5`.  The `ε`/`δ₀` prefix, the `∀ (U1floor, g)` binder order, the
single open door-integral binder at the CONSTANT grade and the conclusion
`¬ logChowla2Fails R.eps R.x R.ω` are byte-identical, and the proof is the landed
proof with the `45` head in place of the landed head.

⟦THE FUSE⟧  `S11Thread.m4_door_contradiction_of_live_split_tower` and
`S11Thread.m4_second_road_tower` thread the landed `^5` conjunct to the road.
Re-running those two proofs against THIS socket (one substitution each, no other
byte) carries `9/2` the rest of the way; nothing else in the register moves. -/
theorem m4_exit_socket_split_45 :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          ((∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
              NearRatTight (arcDen 12 H) H α →
                (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
                  ≤ δ₀ * (H : ℝ)) →
            ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨ε, δ₀, hε, hδ₀, hhead⟩ := log_chowla_two_budget_head_g_45
  refine ⟨ε, δ₀, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨H₀, hH₀⟩ := mrtUniformityXi_of_absWindowBound_twelve ε hε
  obtain ⟨R, hReps, _, hRU1, hRg, hRtow, hR⟩ := hhead 0 (max U1floor H₀) g
  have hU1 : U1floor ≤ R.Hlo := le_trans (le_max_left _ _) hRU1
  have harc : H₀ ≤ R.Hlo := le_trans (le_max_right _ _) hRU1
  refine ⟨R, hReps, hU1, hRg, hRtow, fun hbd => ?_⟩
  exact hR δ₀ hδ₀ le_rfl (m4_exit_of_hbd_split R δ₀ (hH₀ R hReps harc) hbd)

/-- The `9/2` socket implies the landed `^5` socket's payload pointwise: under the
socket's own guard the base is `≥ 50`, so `rpow_nine_halves_le_pow_five` applies.
Recorded so a consumer already wired to the landed shape needs no re-run. -/
theorem tower_conjunct_45_le_five {R : ChowlaRegime}
    (h45 : 50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
      Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) :
    50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
      Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ 5 := by
  intro hu
  exact le_trans (h45 hu) (rpow_nine_halves_le_pow_five (by linarith))

end Salt.MR

end
