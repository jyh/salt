/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦THE `∀ ε` ARM IS THE CROWN'S⟧ — the composition, as a kernel fact
(QUEUE P3 item 11, the design block of 2026-09-05; STATEMENT-ONLY at the freeze)

The 08/31 crown re-tier lists three apex arms above the landed base `logChowla2_v7_rated`:
`∀ ε`, full range, effective `A`.  This file states the first arm's dependency in the kernel:
the crown `MRTDoorAllGrades` (`DoorReceipt.lean:1213` — the `L¹` door at every grade `δ` and
every `ε ≤ 1/2` on regimes above a floor; NO producer) composed with the `ε`-family head
(`SpineEpsFamily.lean`) gives log-Chowla-2 at every `ε ≤ 1/500`, on a regime at that `ε`.
The `L¹ → L²` step is `mrtUniformityXiL2_of_xi` (`MRTDoor.lean:255`, at `K·δ`), with `K` the
head's own exported count bound.

Honest label: CONDITIONAL on the crown, which has no producer and is not claimed reachable
here (its own docstring).  What the statement settles is the SHAPE of the dependency — the
`∀ ε` arm is exactly the door at all grades, nothing more — so the arm is priced by the crown's
price and by nothing on the spine.  Nothing bears on twin primes.
-/
import Salt.MR.DoorReceipt
import Salt.Entropy.Chowla.SpineEpsFamily
import Mathlib

open Salt.Entropy.Chowla

namespace Salt.MR

/-- **E2 (class B) — `∀ ε ≤ 1/500` FROM THE CROWN.**  For every `0 < ε ≤ 1/500` and every floor,
a regime at that `ε` above the floor on which log-Chowla-2 does not fail — given
`MRTDoorAllGrades`.

Recipe: `obtain ⟨K, δ₀, Hcap, hK, hδ₀, hrate, hbody⟩ :=
  log_chowla_two_budget_head_g_sq_count_hloCap_epsFamily ε hε0 hε`; the crown at
`δ := δ₀ / K` (`div_pos hδ₀ hK`), `ε`, `hε0`, `le_trans hε (by norm_num : (1:ℚ)/500 ≤ 1/2)`
gives `H₀` and `hcrown' : ∀ R, R.eps = ε → H₀ ≤ R.Hlo → MRTUniformityXi R (δ₀/K)`;
`hbody (max extraFloor H₀) 0 (fun _ _ => 0)` gives `R` with `R.eps = ε`,
`max extraFloor H₀ ≤ R.Hlo`, the count gate `hXi`, and the door arrow `himpl`;
`mrtUniformityXiL2_of_xi R (le_of_lt (div_pos hδ₀ hK)) hXi
  (hcrown' R hReps (le_trans (le_max_right _ _) hRlo)) : MRTUniformityXiL2 R (K * (δ₀ / K))`;
`mul_div_cancel₀` rewrites the grade to `δ₀`; `himpl δ₀ hδ₀ le_rfl` closes. -/
theorem logChowla2_epsFamily_of_allGrades (hcrown : MRTDoorAllGrades) (ε : ℚ) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 500) (extraFloor : ℕ) :
    ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ ¬ logChowla2Fails R.eps R.x R.ω := by
  sorry

end Salt.MR
