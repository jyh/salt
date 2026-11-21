/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.MillerAlgebraic

/-!
# O106 row R5 — deterministic Miller–Rabin from a small non-member

`deterministicMR_of_smallNonMember : SmallNonMember C → DeterministicMR C`, with no hypothesis
on any `L`-function: for odd composite `n`, Miller's algebraic half (`millerAlgebraic`, R5a) puts
every strong liar in one proper subgroup `H`; `SmallNonMember C` supplies a unit `u ∉ H` with
`2 ≤ u.val < C (log n)²`; if every base below that bound passes, `u` passes, so `u ∈ H`.
GRH enters only through `SmallNonMember` (row R5b, open).
-/

namespace Salt.RH

/-- **R5.** A small unit outside every proper subgroup makes Miller–Rabin deterministic. -/
theorem deterministicMR_of_smallNonMember {C : ℝ} (hS : SmallNonMember C) :
    DeterministicMR C := by
  intro n h3 hodd hpass
  by_contra hnp
  obtain ⟨H, hH, hliar⟩ := millerAlgebraic n h3 hodd hnp
  obtain ⟨u, huH, hu2, huC⟩ := hS n h3 H hH
  haveI : NeZero n := ⟨by omega⟩
  have hun : (u : ZMod n).val < n := ZMod.val_lt _
  exact huH (hliar u (hpass _ hu2 hun huC))

/-- **R5, polylog form.** `SmallNonMemberLog k → DeterministicMRLog k`, by the same argument. -/
theorem deterministicMRLog_of_smallNonMemberLog {k : ℕ} (hS : SmallNonMemberLog k) :
    DeterministicMRLog k := by
  obtain ⟨C, hC⟩ := hS
  refine ⟨C, fun n h3 hodd hpass => ?_⟩
  by_contra hnp
  obtain ⟨H, hH, hliar⟩ := millerAlgebraic n h3 hodd hnp
  obtain ⟨u, huH, hu2, huC⟩ := hC n h3 H hH
  haveI : NeZero n := ⟨by omega⟩
  have hun : (u : ZMod n).val < n := ZMod.val_lt _
  exact huH (hliar u (hpass _ hu2 hun huC))

end Salt.RH
