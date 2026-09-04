/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# λ-BV wave 2-S, step F4a — THE CROWN FED INTO THE AFFINE HEAD (the MR one-liner, F4-S6)

`Salt.Entropy` cannot import `Salt.MR` (the `xceil` fence, H3's lesson), so the affine head
`log_chowla_aff_of_door` (`Salt/Entropy/Chowla/StrideShell.lean`) takes the crown's PAYLOAD as a
binder `hcrown`.  This module is the one place both sides are in scope: it feeds the landed crown
`mrtUniformityXiL2AffW_holds_flat_stride` (`StridePairReceipt.lean:2121`, F3) into that binder.
The result is F4a's single MR-side name — the object F5 consumes: at the crown's regime `Ra`, the
door at grade `a·Zr·ρ + E` AND the entropy-half implication `∀ ρ' ≤ δ₀_aff, door ρ' → ¬ fails`,
side by side, NOT composed (`a·Zr·ρ + E ≤ δ₀_aff` is the `214` miss at `(210, 2)` — F5's
numeral).  Still conditional on the affine circle-method SLOT `hcm` (F4b's producer).

HONEST LABEL.  One class-A application; proves no estimate, closes no prize, bears on nothing on
the apex.  Statement-only at the freeze (sorry-bodied); ⛔ MERGE FENCE with the four Entropy
files of F4a.
-/
import Salt.Entropy.Chowla.StrideShell
import Salt.MR.StridePairReceipt
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **F4-S6 (class A) — the crown fed into the head.**  `log_chowla_aff_of_door a b h ha hh hba
hah7 hcm (fun A₀' => mrtUniformityXiL2AffW_holds_flat_stride a b h ha hh hba hah7 A₀') A₀` — the
crown's conclusion IS the head's `hcrown` binder shape, verbatim. -/
theorem log_chowla_aff_of_door_crowned (a b h : ℕ) (ha : 0 < a) (hh : 0 < h) (hba : b < a)
    (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7)
    (hcm : ∃ C : ℝ, 0 < C ∧ C ≤ (h : ℝ) * (1 + 2 * (2 * Real.log 4)) ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      ((Salt.Entropy.Chowla.primeWindow eps H).card : ℝ)
          ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : Salt.Entropy.Chowla.primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ) else 0|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiAff a b h eps H, (1 / (H : ℝ) ^ 2)
                * ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2))
    (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
        flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
        (∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * ((a * h : ℕ) : ℝ) ^ 2) ∧
          1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
          E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
              * (Real.log (Ra.ω : ℝ) - 1)) ∧
          MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E)) ∧
        ∃ δ₀ : ℝ, 0 < δ₀ ∧ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) ≤ δ₀ ∧
          ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ δ₀ → MRTUniformityXiL2AffW h Ra ρ' →
            ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω := by
  sorry

end Salt.MR
