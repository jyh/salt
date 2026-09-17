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
The `L¹ → L²` step is `mrtUniformityXiL2_of_xi` (`Salt/Entropy/Chowla/MRTDoor.lean:255`,
at `K·δ`), with `K` the head's own exported count bound.

Honest label: CONDITIONAL on the crown, which has no producer and is not claimed reachable
here (its own docstring).  What the statement settles is the SHAPE of the dependency — the
`∀ ε` arm is exactly the door at all grades, nothing more — so the arm is priced by the crown's
price and by nothing on the spine.  Nothing bears on twin primes.  ⚠️ ERRATUM: END OF FILE.
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
  obtain ⟨K, δ₀, Hcap, hK, hδ₀, _hrate, hbody⟩ :=
    log_chowla_two_budget_head_g_sq_count_hloCap_epsFamily ε hε0 hε
  obtain ⟨H₀, hcrown'⟩ := hcrown (δ₀ / K) (div_pos hδ₀ hK) ε hε0
    (le_trans hε (by norm_num : (1 : ℚ) / 500 ≤ 1 / 2))
  obtain ⟨R, hReps, hRlo, _hU1, _hg, hXi, _htow, _hcap, himpl⟩ :=
    hbody (max extraFloor H₀) 0 (fun _ _ => 0)
  refine ⟨R, hReps, le_trans (le_max_left _ _) hRlo, ?_⟩
  have hL2 : MRTUniformityXiL2 R (K * (δ₀ / K)) :=
    mrtUniformityXiL2_of_xi R (le_of_lt (div_pos hδ₀ hK)) hXi
      (hcrown' R hReps (le_trans (le_max_right _ _) hRlo))
  have hKne : K ≠ 0 := ne_of_gt hK
  have heq : K * (δ₀ / K) = δ₀ := by
    field_simp
  rw [heq] at hL2
  exact himpl δ₀ hδ₀ le_rfl hL2

end Salt.MR

/-! ## ⟦ERRATUM TO THE HEADER'S PRICING CLAUSE⟧

⚠️ ERRATUM (2026-09-17, tier-S rung 2 wave 6).  THE HEADER'S SENTENCE IS LEFT IN PLACE AND IS NO
LONGER THE WHOLE PICTURE.  «The `∀ ε` arm is exactly the door at all grades, nothing more» was
true while `Salt.MR.FlatDoorEpsFamilyW` was an uninhabited `Prop`.  It now has a proof —
`flatDoorEpsFamilyW_holds` (`Salt/MR/FlatDoorEpsRung2.lean`) — and through it
`logChowla2_epsFamily_of_flatDoor_floor` (`FlatDoorEpsFamily.lean:224`) reaches E2's conclusion
with `MRTDoorAllGrades` nowhere in its dependency graph.

THE CONCLUSIONS, COMPARED AT THE OBJECT.
* `logChowla2_epsFamily_of_flatDoor_floor` concludes E2's conclusion TOKEN FOR TOKEN —
  `∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ ¬ logChowla2Fails R.eps R.x R.ω` — under
  the same binders in the same order (`(ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
  (extraFloor : ℕ)`).  REGIME: identical, `0 < ε ≤ 1/500`.  QUANTIFIER ORDER: identical.  The
  only difference is the leading hypothesis: `(hcrown : MRTDoorAllGrades)` there,
  `(hW : FlatDoorEpsFamilyW)` here.
* E2′ itself, `logChowla2_epsFamily_of_flatDoor` (`FlatDoorEpsFamily.lean:208`), concludes
  STRICTLY MORE than E2: its floor is a REAL `A₀` with `A₀ ≤ A`, `R.Hlo` is fixed by an EQUALITY
  `R.Hlo = flatDesignBase A` rather than bounded below, and it exports two conjuncts E2 has not,
  `162 ≤ A` and `3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ))`.
* GRADE, which is the substantive difference: E2 reaches the `L²` door by
  `mrtUniformityXiL2_of_xi` from the crown's `L¹` door at EVERY grade, taken at `δ := δ₀ / K`;
  E2′ reads the FLAT door already at the head's own grade `ε/(256·(1 + 4·log 4))` and asks for no
  door at any other grade.

WHAT THIS DOES AND DOES NOT SAY.  E2 is untouched and still true; its `hcrown` binder stands, and
the crown still has no producer.  E2′ and its `_floor` twin still carry
`(hW : FlatDoorEpsFamilyW)` in their TYPES — neither is unconditional AS A STATEMENT — and each
becomes unconditional IN USE by supplying `flatDoorEpsFamilyW_holds`.  What is no longer accurate
is the PRICING clause: the `∀ ε` arm at `ε ≤ 1/500` has a SECOND route that does not pass through
`MRTDoorAllGrades`, so it is not priced by the crown's price alone.  Whether that route touches
the spine is not a claim made here.  Nothing bears on twin primes.
-/
