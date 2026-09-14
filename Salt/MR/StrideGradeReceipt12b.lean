/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# (B1) β W4 H1 — THE GRADED CROWN AT `2^12`, CAP 9, FED INTO THE GRADED HEAD

Build freeze v2 v1.1 (2026-09-13), §3.1 rule 6: the receipt / terminals of β live in THIS new
module (importing `StrideGradeReceipt` and `StridePairReceiptG12b`), the one place both sides of
the `2^12` graded lane are in scope.

`log_chowla_aff_of_door_crowned_unslotted_g12b` is `log_chowla_aff_of_door_crowned_unslotted_g`
(`StrideGradeReceipt.lean:46`) with ONLY the freeze's §3.1 rule-2 raises: the product cap
`log (a·h) ≤ 7 ↦ ≤ 9`, the head `log_chowla_aff_of_door_unslotted_g ↦ …_g12b` and the crown
`mrtUniformityXiL2AffW_holds_flat_stride_g ↦ …_g12b` (ceiling `837782 * 2 ^ 12`); its conclusion
is `GradedAffHeadAt_g12b a b h A₀` (`StridePrize.lean`), the binder
`log_chowla_aff_composed_of_headG_g12b` composes at.  No hypothesis is added: the crown derives
its own stride bound `a ≤ 8103` from the product cap (freeze §3.0).  No landed declaration moves.

HONEST LABEL.  One one-line application at the new names; nothing here proves a new estimate, and
nothing bears on twin primes.
-/
import Salt.MR.StrideGradeReceipt
import Salt.MR.StridePairReceiptG12b
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **⟦β W34 H1⟧ F5-β-S6 at `2^12` and cap 9 — the graded crown fed into the graded unslotted head,
concluding `GradedAffHeadAt_g12b`.**  `log_chowla_aff_of_door_crowned_unslotted_g`
(StrideGradeReceipt.lean:46) at the `_g12b` names (census band 4 row 14: SUPPLIER-SWAP):
`unfold GradedAffHeadAt_g12b; exact log_chowla_aff_of_door_unslotted_g12b a b h ha hh hba hgcd hah9
(fun A₀' => mrtUniformityXiL2AffW_holds_flat_stride_g12b a b h ha hh hba hah9 A₀') A₀`.  The
`unfold` is the K-check: `GradedAffHeadAt_g12b`'s body must be the graded head's conclusion byte for
byte. -/
theorem log_chowla_aff_of_door_crowned_unslotted_g12b (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hba : b < a) (hgcd : Nat.gcd (b + h) a ∣ h)
    (hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9) (A₀ : ℝ) :
    GradedAffHeadAt_g12b a b h A₀ := by
  unfold GradedAffHeadAt_g12b
  exact log_chowla_aff_of_door_unslotted_g12b a b h ha hh hba hgcd hah9
    (fun A₀' => mrtUniformityXiL2AffW_holds_flat_stride_g12b a b h ha hh hba hah9 A₀') A₀

end Salt.MR
