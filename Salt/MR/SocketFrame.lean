/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The M4 row frame at a socket base

The three socket predicates `SocketBase`, `SocketBaseL` and `SocketBaseLH` all open with the
same eight-place prefix `Hlo ≤ H ∧ H ≤ Hhi ∧ L ≤ H ∧ 0 < q ∧ _ ∧ _ ∧ _ ∧ 0 < A ∧ _`. Every M4
row instance projects `0 < q` and `0 < A` out of that prefix and then derives, by hand, the
three facts its row slot reads: `0 < A + s`, its real cast, and `2·(A + s) ≤ 4·(A + s)` at the
casts. This file states those five facts once, over the prefix's shape, so one lemma serves all
three predicates.

The 25 call sites that took them inline are in `M4RowAssemblyLinear`, `M4RowSpineLinear`,
`M4RowsChiEnd`, `M4RowsChiEndPrime`, `M4RowsChiPrimeLinear`, `M4RowsChiZero`,
`M4RowsChiZeroPrime`, `NumeralCt`, `S16ComposeLH` and `S16ProducersH`; there they are used as
`hq`, `hA`, `hAs`, `hAsR` and `hN4`. The lemma is over propositions and naturals and imports
nothing beyond Mathlib; a socket predicate meets its hypothesis by unfolding.

## Main results
* `socketFrame_facts` — the five frame facts from the socket prefix.
-/

namespace Salt.MR

/-- **The M4 row frame.** From a socket prefix carrying `0 < q` in fourth place and `0 < A` in
eighth: `0 < q`, `0 < A`, `0 < A + s`, `(0 : ℝ) < ↑(A + s)` and `↑(2·(A + s)) ≤ 4·↑(A + s)`. -/
theorem socketFrame_facts {P₁ P₂ P₃ P₅ P₆ P₇ R : Prop} {q A : ℕ} (s : ℕ)
    (hb : P₁ ∧ P₂ ∧ P₃ ∧ 0 < q ∧ P₅ ∧ P₆ ∧ P₇ ∧ 0 < A ∧ R) :
    0 < q ∧ 0 < A ∧ 0 < A + s ∧ (0 : ℝ) < (((A + s : ℕ)) : ℝ) ∧
      (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  exact ⟨hb.2.2.2.1, hA, hAs, hAsR, by push_cast; linarith⟩

end Salt.MR
