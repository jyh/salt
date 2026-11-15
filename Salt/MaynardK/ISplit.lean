/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.MvSplit
import Salt.Twelve.DecBoxPair

/-!
# C1 · B4.2a — `mv_I_split` at general `k` for a budget polynomial (`mv_I_split_gen`)

The index set `k = 5 → k`, `sq (ofPoly F) → P`, `^ 5 → ^ k`, the `40 = 2·C(5,2)·2` collision
constant → `2k²` (pair count `≤ k²`, never `decide` on a card). `mv_I_split_of_gen` (in `Controls`)
recovers the landed statement. Ported by an Opus executor from a frozen brief (2026-10-11).
-/

open Finset

namespace Salt.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Salt.Twelve

open Salt.Maynard

/-! ## `mv_I_split` -/

omit [Salt.Maynard.TupleChoice] in
/-- `mv_I_split` at general `k ≥ 2` for a budget polynomial `P`, under its landed name: the proof is
`Salt.Twelve.mv_I_split_k` (MvSplit), whose `k = 5` instance is `Salt.Twelve.mv_I_split`. -/
theorem mv_I_split_gen (k : ℕ) (hk : 2 ≤ k) (P : BPoly k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ kSieveIndex k R W',
              eval P (fun i => Real.log (r i) / Real.log R)
                / ∏ i, (Nat.totient (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ k
              * ((simplexInt P : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ k / Real.log R
          + A * (1 + Salt.Maynard.phiAtomSum R W') ^ k / D :=
  Salt.Twelve.mv_I_split_k k hk P

/-! ## Helpers for `inner_contract_rel` (private copies from `MvJ.lean`) -/

end Salt.MaynardK
