/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The eight-arm design constant's floors, from its `max` definition

The Ks-windowed door assemblies mint their design constant in two steps,
`A' = max s (max T₀ (max (max (max (max A₀ 162) Awin) c) (max b (max (4·x) H))))` and then
`A = max k A'` (the eighth arm `k = armVt Kvt` outermost), and then read off, each time by hand,
that `A` lies above each of the ten arguments. This file states those facts once.

The ten call sites that took them inline are `DoorReceipt`, `DoorReceiptSiegelFree`,
`FlatDoorEpsChain`, `StridePairReceipt`, `StridePairReceiptG`, `StridePairReceiptG12b`,
`TierSBand`, `V7Rated`, `V7RatedH` and `V7SiegelFree`; at each one `s = 16·log (1/Ks)/3`,
`c = cofkRThr Cq Cb Xsk Y0`, `b = budgetAFlat ε β`, and `x = x₀` and `H = Hopq` are casts of
naturals, and the facts are used as `harmA`, `hKsA`, `hT₀A`, `hA162`, `hA₀A`, `hAwinA`, `hthrA`,
`hAge`, `hx0A` and `hopqA`. The lemma is over reals and imports nothing beyond Mathlib.

## Main results
* `designEightArms_facts` — the ten floors of the two-step `max` design constant.
-/

namespace Salt.MR

/-- **The eight-arm design constant's floors.** For
`A' = max s (max T₀ (max (max (max (max A₀ 162) Awin) c) (max b (max (4·x) H))))` and
`A = max k A'`: `A` lies above `k`, `s`, `T₀`, `162`, `A₀`, `Awin`, `c`, `b`, `4·x` and `H`. -/
theorem designEightArms_facts {A A' k s T₀ A₀ Awin c b x H : ℝ}
    (hA'def : A' = max s (max T₀ (max (max (max (max A₀ 162) Awin) c) (max b (max (4 * x) H)))))
    (hAdef : A = max k A') :
    k ≤ A ∧ s ≤ A ∧ T₀ ≤ A ∧ (162 : ℝ) ≤ A ∧ A₀ ≤ A ∧ Awin ≤ A ∧ c ≤ A ∧ b ≤ A ∧
      4 * x ≤ A ∧ H ≤ A := by
  subst hA'def hAdef
  simp only [le_max_iff, le_refl, true_or, or_true, and_self]

end Salt.MR
